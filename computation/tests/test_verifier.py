"""Negative controls for the exact certificate checker and Lean-data bridge."""

import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

CODE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(CODE))
import verify
import check_lean_data


def first(node, kind):
    if node["kind"] == kind:
        return node
    if node["kind"] == "split":
        return first(node["left"], kind) or first(node["right"], kind)
    return None


class CertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.canonical = verify.load_json(CODE / "data/pair_trees.json")

    def setUp(self):
        self.data = copy.deepcopy(self.canonical)

    def rejected(self, match=None):
        with self.assertRaisesRegex(ValueError, match or "."):
            verify.replay(self.data)

    def test_valid_full_cover(self):
        report = verify.replay(self.data)
        self.assertEqual((report["cases"], report["nodes"], report["leaves"]), (19, 6795, 3407))

    def test_missing_case(self):
        self.data["cases"].pop()
        self.rejected("Missing")

    def test_duplicate_case(self):
        self.data["cases"][-1] = copy.deepcopy(self.data["cases"][0])
        self.rejected("duplicated")

    def test_wrong_surplus(self):
        self.data["surplus"] = "1/8000"
        self.rejected("surplus")

    def test_wrong_gamma(self):
        self.data["gamma_upper"] = "1/8"
        self.rejected("gamma")

    def test_boolean_multiplicity(self):
        self.data["cases"][0]["m"] = True
        self.rejected("integer")

    def test_float_statistic(self):
        self.data["case_count"] = 19.0
        self.rejected("integer")

    def test_noncanonical_rational(self):
        self.data["cases"][0]["root_box"]["c"][0] = "2/6"
        self.rejected("Noncanonical")

    def test_wrong_root_domain(self):
        self.data["cases"][0]["root_box"]["c"][0] = "1/4"
        self.rejected("root domain")

    def test_missing_child(self):
        del self.data["cases"][0]["tree"]["right"]
        self.rejected("two children")

    def test_gap_at_split(self):
        self.data["cases"][0]["tree"]["midpoint"] = "1/3"
        self.rejected("midpoint")

    def test_wrong_split_axis(self):
        self.data["cases"][0]["tree"]["axis"] = "z"
        self.rejected("axis")

    def test_unsupported_projection_on_full_square(self):
        self.data["cases"][0]["tree"] = {"kind": "projection"}
        self.rejected("Projection inequality")

    def test_strip_threshold_missing_upper_witness(self):
        first(self.data["cases"][0]["tree"], "strip")["T"] = "0/1"
        self.rejected("upper-angle")

    def test_strip_threshold_outside_domain(self):
        first(self.data["cases"][0]["tree"], "strip")["T"] = "2/1"
        self.rejected("outside")

    def test_full_angle_threshold_fails_strip_inequality(self):
        first(self.data["cases"][0]["tree"], "strip")["T"] = "1/1"
        self.rejected("Strip exclusion")

    def test_wrong_case_statistics(self):
        self.data["cases"][0]["counts"]["leaves"] += 1
        self.rejected("statistics")

    def test_unrecognized_leaf_field(self):
        first(self.data["cases"][0]["tree"], "strip")["accepted"] = True
        self.rejected("strip fields")

    def test_duplicate_json_keys_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "duplicate.json"
            path.write_text('{"surplus":"1/4000","surplus":"1/8000"}')
            with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
                verify.load_json(path)

    def test_nonfinite_json_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "nan.json"
            path.write_text('{"x":NaN}')
            with self.assertRaisesRegex(ValueError, "Non-JSON"):
                verify.load_json(path)

    def test_certificate_checksum_binding(self):
        manifest = verify.load_json(CODE / "manifest.json")
        manifest["certificate"]["sha256"] = "0" * 64
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "manifest.json"
            path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, "Certificate checksum mismatch"):
                verify.verify_locked(CODE / "data/pair_trees.json", path)

    def test_manuscript_checksum_binding(self):
        manifest = verify.load_json(CODE / "manifest.json")
        manifest["manuscript"]["path"] = str((CODE / manifest["manuscript"]["path"]).resolve())
        manifest["manuscript"]["sha256"] = "0" * 64
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "manifest.json"
            path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, "Manuscript checksum mismatch"):
                verify.verify_locked(CODE / "data/pair_trees.json", path)

    def test_lean_bridge_rejects_changed_tree(self):
        with tempfile.TemporaryDirectory() as directory:
            lean = Path(directory)
            path = lean / "CubeSections/Certificates/Data/Q2M1L1.lean"
            path.parent.mkdir(parents=True)
            path.write_text("def parameters : Parameters := ⟨2, 1, 1⟩\n"
                            "private def node_0 : Tree := .leaf .projection\n"
                            "def tree : Tree := node_0\n")
            with self.assertRaisesRegex(ValueError, "Lean/JSON tree mismatch"):
                check_lean_data.compare(self.data, lean)


if __name__ == "__main__":
    unittest.main()
