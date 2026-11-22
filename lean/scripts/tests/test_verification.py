"""Regression tests for cache integrity and fail-closed contract checking."""

import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import verification as verification
from check import accepted_axioms, normalize_axiom_name, parse_axioms


class CacheIntegrity(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.output = Path(self.directory.name) / "Example.olean"
        self.output.write_bytes(b"original producing output")
        self.inputs = {"source_sha256": "source", "compiler_context": "compiler-and-pins",
                       "dependencies": {"CubeSections.Base": {
                           "output_sha256": "base-output", "input_fingerprint": "base-inputs"}}}
        self.receipt = {"schema": "msc-build-module/1", "exit_code": 0,
                        "source_unchanged": True, "inputs_unchanged": True,
                        "inputs": copy.deepcopy(self.inputs),
                        "output_sha256": verification.sha(self.output)}

    def tearDown(self):
        self.directory.cleanup()

    def test_original_producing_output_is_reused(self):
        self.assertTrue(verification.cached_result_matches(self.receipt, self.inputs, self.output))

    def test_modified_output_is_rejected_even_when_inputs_match(self):
        self.output.write_bytes(b"different object with unchanged source and dependency metadata")
        self.assertFalse(verification.cached_result_matches(self.receipt, self.inputs, self.output))

    def test_transitive_input_change_rejected_even_if_direct_output_stays_same(self):
        self.inputs["dependencies"]["CubeSections.Base"]["input_fingerprint"] = "different-ancestor-input"
        self.assertFalse(verification.cached_result_matches(self.receipt, self.inputs, self.output))

    def test_compiler_or_dependency_pins_change_is_rejected(self):
        self.inputs["compiler_context"] = "different-compiler-or-pins"
        self.assertFalse(verification.cached_result_matches(self.receipt, self.inputs, self.output))

    def test_missing_output_and_failed_receipt_are_rejected(self):
        self.receipt["exit_code"] = 1
        self.assertFalse(verification.cached_result_matches(self.receipt, self.inputs, self.output))
        self.receipt["exit_code"] = 0
        self.output.unlink()
        self.assertFalse(verification.cached_result_matches(self.receipt, self.inputs, self.output))

    def test_changed_inputs_during_compilation_are_rejected(self):
        self.receipt["inputs_unchanged"] = False
        self.assertFalse(verification.cached_result_matches(self.receipt, self.inputs, self.output))


class ContractChecks(unittest.TestCase):
    def test_missing_axiom_report_is_failure(self):
        reports = parse_axioms("'Good' depends on axioms: [propext, Classical.choice, Quot.sound]")
        self.assertTrue(accepted_axioms(reports, ["Good"]))
        self.assertFalse(accepted_axioms(reports, ["Good", "Missing"]))

    def test_unapproved_axiom_is_failure(self):
        reports = parse_axioms("'Bad' depends on axioms: [propext, ExtraUnapprovedAxiom]")
        self.assertFalse(accepted_axioms(reports, ["Bad"]))

    def test_target_manifest_cannot_omit_a_contract_or_add_an_axiom(self):
        manifest = verification.check_targets()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            changed = copy.deepcopy(manifest)
            changed["mandatory_targets"].pop()
            (root / "target_manifest.json").write_text(json.dumps(changed))
            with self.assertRaises(ValueError):
                verification.check_targets(root)
            changed = copy.deepcopy(manifest)
            changed["allowed_axioms"].append("ExtraUnapprovedAxiom")
            (root / "target_manifest.json").write_text(json.dumps(changed))
            with self.assertRaises(ValueError):
                verification.check_targets(root)

    def test_nested_comments_and_strings_do_not_create_imports(self):
        text = '/- import Fake\n /- nested -/ -/\nimport CubeSections.Semantics\ndef s := "import FakeAgain"\n'
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Example.lean"
            source.write_text(text)
            self.assertEqual(verification.imports(source), ["CubeSections.Semantics"])



class UniversePrintedAxioms(unittest.TestCase):
    def test_standard_axioms_with_pp_universes(self):
        reports = parse_axioms("'Good' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u_1}]")
        self.assertEqual(reports["Good"], verification.ALLOWED_AXIOMS)
        self.assertTrue(accepted_axioms(reports, ["Good"]))

    def test_well_formed_level_expressions_and_commas_are_syntax_only(self):
        self.assertEqual(normalize_axiom_name("Classical.choice.{(max u (v + 1))}"), "Classical.choice")
        reports = parse_axioms("'Unknown' depends on axioms: [OtherAxiom.{u, v}, propext]")
        self.assertEqual(reports["Unknown"], {"OtherAxiom", "propext"})
        self.assertFalse(accepted_axioms(reports, ["Unknown"]))

    def test_near_matches_never_become_standard_names(self):
        for name in ["Classical.choiceExtra.{u}", "Classical.choice.extra.{u}",
                     "_root_.Classical.choice.{u}", "Quot.soundness.{u}", "propextExtra"]:
            with self.subTest(name=name):
                reports = parse_axioms("'Bad' depends on axioms: [" + name + "]")
                self.assertFalse(accepted_axioms(reports, ["Bad"]))

    def test_malformed_suffixes_fail_closed(self):
        for name in ["Classical.choice.{}", "Classical.choice.{u", "Classical.choice.{u}.extra",
                     "Classical.choice.{u;garbage}", "Classical.choice.{u,}",
                     "Classical.choice.{(u}", "Classical.choice.{max u}",
                     "Classical.choice.{u + v}", "Classical.choice.{{u}}"]:
            with self.subTest(name=name):
                with self.assertRaises(ValueError):
                    parse_axioms("'Bad' depends on axioms: [" + name + "]")

    def test_unknown_axiom_is_rejected_even_with_valid_universe_suffix(self):
        reports = parse_axioms("'Bad' depends on axioms: [propext, ExtraUnapprovedAxiom.{u}]")
        self.assertFalse(accepted_axioms(reports, ["Bad"]))

    def test_duplicate_reports_cannot_erase_an_unapproved_axiom(self):
        reports = parse_axioms("'Bad' depends on axioms: [ExtraUnapprovedAxiom.{u}]\n"
                               "'Bad' depends on axioms: [propext]\n"
                               "'Bad' does not depend on any axioms")
        self.assertFalse(accepted_axioms(reports, ["Bad"]))

    def test_incomplete_lists_and_empty_entries_fail_closed(self):
        for output in ["'Bad' depends on axioms: [propext", "'Bad' depends on axioms: [propext,]",
                       "'Bad' depends on axioms: [,propext]"]:
            with self.subTest(output=output):
                with self.assertRaises(ValueError):
                    parse_axioms(output)

    def test_empty_axiom_list_remains_valid(self):
        reports = parse_axioms("'Good' depends on axioms: []")
        self.assertEqual(reports["Good"], set())
        self.assertTrue(accepted_axioms(reports, ["Good"]))


if __name__ == "__main__":
    unittest.main()
