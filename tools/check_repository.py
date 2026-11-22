#!/usr/bin/env python3
"""Check release hashes and high-confidence publication hygiene constraints.

This is a source-package check, not a Lean proof check or certificate verifier.
Run those checks separately as described in the repository README.
"""

import argparse
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import release_manifest


FORBIDDEN_TEXT = {
    "private workspace path": re.compile(r"/workspac[e]/"),
    "private agent home path": re.compile(r"/home/agen[t](?:/|\b)"),
    "session download link": re.compile(r"sandbo[x]:", re.IGNORECASE),
    "private file identifier": re.compile(r"libfil[e]_"),
    "private storage URI": re.compile(r"oai-librar[y](?:://)?", re.IGNORECASE),
    "GitHub credential": re.compile(r"\bgh[pousr]_[A-Za-z0-9]{20,}\b"),
}
ARCHIVE_SUFFIXES = {".zip", ".tar", ".gz", ".bz2", ".xz", ".7z", ".rar"}


def check(root):
    manifest = release_manifest.check(root)
    files, inventory_errors = release_manifest.inventory(root)
    violations = []
    for relative in files:
        path = root / relative
        if path.is_symlink():
            violations.append({"file": relative, "reason": "Source symlink"})
            continue
        if path.suffix.lower() in ARCHIVE_SUFFIXES:
            violations.append({"file": relative, "reason": "Archive in publication source tree"})
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            violations.append({"file": relative, "reason": "Cannot read UTF-8 source: " + str(error)})
            continue
        if "\x00" in text:
            violations.append({"file": relative, "reason": "NUL byte in text source"})
        for label, pattern in FORBIDDEN_TEXT.items():
            for match in pattern.finditer(text):
                # Do not echo a matched credential or private path into the report.
                violations.append({"file": relative, "line": text.count("\n", 0, match.start()) + 1,
                                   "reason": label})
    return {"status": "PASS" if manifest["status"] == "PASS" and not violations and
            not inventory_errors else "FAIL", "manifest": manifest,
            "hygiene_files_checked": len(files), "hygiene_violations": violations,
            "scope": "Source integrity and publication hygiene only; mathematical checks are separate."}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args(argv)
    root = args.root.resolve()
    try:
        if not root.is_dir():
            raise ValueError("Repository root is not a directory")
        result = check(root)
    except (OSError, UnicodeError, ValueError) as error:
        result = {"status": "FAIL", "errors": [str(error)]}
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
