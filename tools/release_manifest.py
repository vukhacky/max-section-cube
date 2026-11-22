#!/usr/bin/env python3
"""Write or check the SHA-256 inventory of the publication source tree.

The manifest covers the explicitly selected text sources, configuration, data,
and verification records. Build products and local execution directories are
excluded. Verification never refreshes the manifest: update it with ``write``
only after reviewing and checking an intentional source change.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import sys


SCHEMA = "max-section-cube-release/v1"
MANIFEST = "release_manifest.json"
ROOT_FILES = {
    "README.md", "CITATION.cff", ".gitignore", ".gitattributes", "LICENSE", "LICENSE.md",
    "COPYING", "Makefile", "CHANGELOG.md", "REPRODUCE.md",
}
SOURCE_DIRS = {"lean", "computation", "manuscript", "docs", "verification", "tools", ".github"}
EXTENSIONS = {
    "lean": {".lean", ".py", ".json", ".toml", ".md", ".txt", ".sh"},
    "computation": {".py", ".json", ".toml", ".md", ".txt", ".sh"},
    "manuscript": {".tex", ".md"},
    "docs": {".md", ".json"},
    "verification": {".md", ".json", ".log", ".txt", ".py", ".lean", ".sh"},
    "tools": {".py", ".sh", ".md", ".json"},
    ".github": {".yml", ".yaml", ".md"},
}
IGNORED_DIRS = {
    ".git", ".lake", "__pycache__", ".venv", "venv", ".pytest_cache",
    ".publiclogs", "build", "dist",
}
BUILD_SUFFIXES = {
    ".olean", ".ilean", ".trace", ".pyc", ".pyo", ".pyd", ".o", ".so", ".a",
    ".aux", ".out", ".toc", ".bbl", ".blg", ".fls", ".fdb_latexmk", ".pdf",
}
SPECIAL_FILES = {"lean/lean-toolchain"}
MAX_VERIFICATION_BYTES = 16 * 1024 * 1024


def ignored(relative):
    """Local outputs are deliberately outside the publication source inventory."""
    p = PurePosixPath(relative)
    if any(part in IGNORED_DIRS for part in p.parts):
        return True
    if p.parts[:2] in {
        ("verification", "runs"), ("computation", "output"),
        ("computation", ".cache"), ("lean", ".audit"),
    }:
        return True
    if len(p.parts) == 2 and p.parts[0] == "manuscript" and p.suffix == ".log":
        return True
    if p.name == ".DS_Store" or p.name.endswith("~") or p.suffix == ".swp":
        return True
    if p.parts[:2] == ("verification", "external") and (
        p.name.endswith(".ndjson") or p.name.endswith(".ndjson.gz")
    ):
        return True
    return p.suffix in BUILD_SUFFIXES or p.name.endswith(".synctex.gz")


def selected(relative):
    p = PurePosixPath(relative)
    if relative in ROOT_FILES or relative in SPECIAL_FILES:
        return True
    return len(p.parts) > 1 and p.parts[0] in SOURCE_DIRS and p.suffix in EXTENSIONS[p.parts[0]]


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def inventory(root):
    """Return selected file hashes and errors; never follow source symlinks."""
    files, errors = {}, []
    for current, dirs, names in os.walk(root, followlinks=False):
        current = Path(current)
        retained = []
        for name in sorted(dirs):
            path = current / name
            rel = path.relative_to(root).as_posix()
            if ignored(rel):
                continue
            if path.is_symlink():
                errors.append("Source directory is a symlink: " + rel)
            elif current == root and name not in SOURCE_DIRS:
                errors.append("Unselected top-level directory: " + rel)
            else:
                retained.append(name)
        dirs[:] = retained
        for name in sorted(names):
            path = current / name
            rel = path.relative_to(root).as_posix()
            if rel == MANIFEST or ignored(rel):
                continue
            if path.is_symlink():
                errors.append("Source file is a symlink: " + rel)
                continue
            if not selected(rel):
                errors.append("File is outside the publication source policy: " + rel)
                continue
            size = path.stat().st_size
            if rel.startswith("verification/") and size > MAX_VERIFICATION_BYTES:
                errors.append("Verification record exceeds 16 MiB: " + rel)
                continue
            files[rel] = {"sha256": digest(path), "bytes": size}
    return dict(sorted(files.items())), errors


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("Duplicate JSON key: " + key)
        result[key] = value
    return result


def load_manifest(path):
    if path.is_symlink():
        raise ValueError("Manifest is a symlink")
    value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_object)
    if not isinstance(value, dict) or value.get("schema") != SCHEMA:
        raise ValueError("Missing or unsupported manifest schema")
    if value.get("hash_algorithm") != "sha256" or value.get("source_policy") != "source-v1":
        raise ValueError("Unsupported hash algorithm or source policy")
    entries = value.get("files")
    if not isinstance(entries, dict) or not entries:
        raise ValueError("Manifest files must be a nonempty object")
    for name, entry in entries.items():
        p = PurePosixPath(name)
        if (not name or "\\" in name or p.is_absolute() or ".." in p.parts or
                str(p) != name or ignored(name) or not selected(name)):
            raise ValueError("Invalid or excluded manifest path: " + name)
        if (not isinstance(entry, dict) or set(entry) != {"sha256", "bytes"} or
                not isinstance(entry["sha256"], str) or
                not re.fullmatch(r"[0-9a-f]{64}", entry["sha256"]) or
                type(entry["bytes"]) is not int or entry["bytes"] < 0):
            raise ValueError("Invalid manifest entry: " + name)
    if value.get("file_count") != len(entries):
        raise ValueError("Manifest file_count disagrees with its entries")
    return value


def check(root):
    current, errors = inventory(root)
    result = {"status": "FAIL", "files_checked": len(current), "errors": errors,
              "missing": [], "unlisted": [], "changed": []}
    try:
        expected = load_manifest(root / MANIFEST)["files"]
    except (OSError, UnicodeError, ValueError) as error:
        result["errors"].append("Cannot validate manifest: " + str(error))
        return result
    result["missing"] = sorted(set(expected) - set(current))
    result["unlisted"] = sorted(set(current) - set(expected))
    result["changed"] = sorted(name for name in set(current) & set(expected)
                               if current[name] != expected[name])
    if not any(result[k] for k in ("errors", "missing", "unlisted", "changed")):
        result["status"] = "PASS"
    return result


def write(root):
    files, errors = inventory(root)
    if errors or not files:
        return {"status": "FAIL", "errors": errors or ["No publication source files found"]}
    path = root / MANIFEST
    if path.is_symlink():
        return {"status": "FAIL", "errors": ["Refusing to replace a symlink manifest"]}
    value = {"schema": SCHEMA, "hash_algorithm": "sha256", "source_policy": "source-v1",
             "file_count": len(files), "files": files}
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return {"status": "PASS", "action": "write", "files_recorded": len(files), "manifest": MANIFEST}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("write", "check"))
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args(argv)
    root = args.root.resolve()
    if not root.is_dir():
        result = {"status": "FAIL", "errors": ["Repository root is not a directory"]}
    else:
        try:
            result = write(root) if args.action == "write" else check(root)
        except (OSError, UnicodeError, ValueError) as error:
            result = {"status": "FAIL", "errors": [str(error)]}
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
