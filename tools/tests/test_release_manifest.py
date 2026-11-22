"""Positive and negative controls for publication integrity and hygiene.

Run from the repository root:
    python3 -m unittest discover -s tools/tests -v
"""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
import check_repository as hygiene
import release_manifest as manifest


class ReleaseManifestTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="msc-release-test-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.put("README.md", "# A miniature publication\n")
        self.put("lean/lean-toolchain", "leanprover/lean4:v4.37.0-rc1\n")
        self.put("computation/data/case.json", '{"exact":true}\n')
        self.assertEqual(manifest.write(self.root)["status"], "PASS")

    def put(self, relative, text):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        return path

    def test_initial_explicit_write(self):
        (self.root / manifest.MANIFEST).unlink()
        result = manifest.write(self.root)
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(result["files_recorded"], 3)

    def test_unchanged_source_passes(self):
        self.assertEqual(manifest.check(self.root)["status"], "PASS")
        self.assertEqual(hygiene.check(self.root)["status"], "PASS")

    def test_changed_source_rejected(self):
        self.put("README.md", "Changed source\n")
        result = manifest.check(self.root)
        self.assertEqual(result["status"], "FAIL")
        self.assertEqual(result["changed"], ["README.md"])

    def test_check_never_refreshes(self):
        path = self.root / manifest.MANIFEST
        original = path.read_bytes()
        self.put("README.md", "Changed source\n")
        self.assertEqual(manifest.check(self.root)["status"], "FAIL")
        self.assertEqual(path.read_bytes(), original)

    def test_explicit_update_restores_pass(self):
        self.put("README.md", "Reviewed changed source\n")
        self.assertEqual(manifest.check(self.root)["status"], "FAIL")
        self.assertEqual(manifest.write(self.root)["status"], "PASS")
        self.assertEqual(manifest.check(self.root)["status"], "PASS")

    def test_unlisted_source_rejected(self):
        self.put("tools/new.py", "print(1)\n")
        result = manifest.check(self.root)
        self.assertEqual(result["status"], "FAIL")
        self.assertEqual(result["unlisted"], ["tools/new.py"])

    def test_gitattributes_is_manifest_source(self):
        self.put(".gitattributes", "* text=auto eol=lf\n")
        result = manifest.check(self.root)
        self.assertEqual(result["status"], "FAIL")
        self.assertEqual(result["unlisted"], [".gitattributes"])
        self.assertEqual(manifest.write(self.root)["status"], "PASS")
        self.assertEqual(manifest.check(self.root)["status"], "PASS")
        self.put(".gitattributes", "* text=auto\n")
        self.assertEqual(manifest.check(self.root)["changed"], [".gitattributes"])

    def test_missing_source_rejected(self):
        (self.root / "computation/data/case.json").unlink()
        result = manifest.check(self.root)
        self.assertEqual(result["status"], "FAIL")
        self.assertEqual(result["missing"], ["computation/data/case.json"])

    def test_documented_local_outputs_excluded(self):
        for path in ["lean/.lake/build/Case.olean", "computation/__pycache__/case.pyc",
                     "verification/runs/local.log", "verification/external/targets.ndjson"]:
            self.put(path, "local generated output")
        self.assertEqual(manifest.check(self.root)["status"], "PASS")

    def test_archive_in_source_rejected(self):
        self.put("docs/private_archive.zip", "archive is outside the source policy")
        self.assertEqual(hygiene.check(self.root)["status"], "FAIL")

    def test_source_file_symlink_rejected(self):
        path = self.root / "docs/link.md"
        path.parent.mkdir()
        try:
            path.symlink_to(self.root / "README.md")
        except (OSError, NotImplementedError) as error:
            self.skipTest("Symlink creation is unavailable: " + str(error))
        self.assertEqual(hygiene.check(self.root)["status"], "FAIL")

    def test_source_directory_symlink_rejected(self):
        path = self.root / "docs/linkdir"
        path.parent.mkdir()
        try:
            path.symlink_to(self.root / "computation", target_is_directory=True)
        except (OSError, NotImplementedError) as error:
            self.skipTest("Symlink creation is unavailable: " + str(error))
        self.assertEqual(hygiene.check(self.root)["status"], "FAIL")

    def test_mathematical_open_axiom_words_allowed(self):
        self.put("README.md", "Ordinary mathematical terms: open set, axiom audit.\n")
        self.assertEqual(manifest.write(self.root)["status"], "PASS")
        self.assertEqual(hygiene.check(self.root)["status"], "PASS")

    def test_forged_digest_rejected(self):
        path = self.root / manifest.MANIFEST
        value = json.loads(path.read_text())
        value["files"]["README.md"]["sha256"] = "0" * 64
        path.write_text(json.dumps(value))
        self.assertEqual(manifest.check(self.root)["status"], "FAIL")

    def test_duplicate_manifest_keys_rejected(self):
        (self.root / manifest.MANIFEST).write_text('{"schema":"x","schema":"y"}')
        self.assertEqual(manifest.check(self.root)["status"], "FAIL")

    def test_public_check_cli_exit_zero(self):
        for script, actions in [("release_manifest.py", ["check"]), ("check_repository.py", [])]:
            run = subprocess.run([sys.executable, str(TOOLS / script), *actions,
                                  "--root", str(self.root)], capture_output=True, text=True)
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr)

    def test_public_check_cli_exit_nonzero_on_change(self):
        self.put("README.md", "Changed after manifest\n")
        run = subprocess.run([sys.executable, str(TOOLS / "check_repository.py"),
                              "--root", str(self.root)], capture_output=True, text=True)
        self.assertNotEqual(run.returncode, 0)

    def test_computation_output_excluded(self):
        self.put("computation/output/replay.json", '{"local":true}\n')
        self.assertEqual(manifest.check(self.root)["status"], "PASS")

    def test_computation_cache_excluded(self):
        self.put("computation/.cache/lookup.json", '{"local":true}\n')
        self.assertEqual(manifest.check(self.root)["status"], "PASS")

    def test_pytest_cache_excluded(self):
        self.put(".pytest_cache/state.json", '{"local":true}\n')
        self.assertEqual(manifest.check(self.root)["status"], "PASS")

    def test_lean_audit_outputs_excluded(self):
        self.put("lean/.audit/receipt.json", '{"local":true}\n')
        self.assertEqual(manifest.check(self.root)["status"], "PASS")

    def test_manuscript_build_log_excluded(self):
        self.put("manuscript/paper.log", "Local TeX build\n")
        self.assertEqual(manifest.check(self.root)["status"], "PASS")

    def test_verification_log_is_tracked(self):
        self.put("verification/check.log", "Verified result\n")
        result = manifest.check(self.root)
        self.assertEqual(result["status"], "FAIL")
        self.assertEqual(result["unlisted"], ["verification/check.log"])
        self.assertEqual(manifest.write(self.root)["status"], "PASS")
        self.put("verification/check.log", "Altered result\n")
        self.assertEqual(manifest.check(self.root)["changed"], ["verification/check.log"])

    def test_editor_artifacts_excluded(self):
        for path in [".DS_Store", "README.md~", "computation/verify.py.swp"]:
            self.put(path, "local editor output")
        self.assertEqual(manifest.check(self.root)["status"], "PASS")

    def test_compiled_trace_artifacts_excluded(self):
        for path in ["lean/local.trace", "computation/module.pyd"]:
            self.put(path, "local compiled output")
        self.assertEqual(manifest.check(self.root)["status"], "PASS")


# Assemble artificial forbidden values at runtime so the test source itself is
# suitable for publication and does not look like a leaked private identifier.
LEAK_VALUES = {
    "workspace": "/" + "workspace/example/file",
    "agent_home": "/" + "home/" + "agent/example",
    "session_link": "sand" + "box:/example",
    "file_identifier": "lib" + "file_example",
    "storage_uri": "oai-" + "library://example",
    "credential": "gh" + "p_" + "A" * 24,
}


def leak_test(value, check_redaction):
    def test(self):
        self.put("README.md", value + "\n")
        self.assertEqual(manifest.write(self.root)["status"], "PASS")
        result = hygiene.check(self.root)
        self.assertEqual(result["status"], "FAIL")
        self.assertTrue(result["hygiene_violations"])
        if check_redaction:
            self.assertNotIn(value, json.dumps(result))
    return test


for label, value in LEAK_VALUES.items():
    setattr(ReleaseManifestTests, "test_private_leak_" + label + "_rejected", leak_test(value, False))
    setattr(ReleaseManifestTests, "test_private_leak_" + label + "_not_echoed", leak_test(value, True))


if __name__ == "__main__":
    unittest.main()
