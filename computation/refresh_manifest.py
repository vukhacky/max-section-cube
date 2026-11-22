#!/usr/bin/env python3
"""Refresh source/data checksums after an intentional reviewed change.

This records provenance; it does not approve changes to mathematical statements.
The exact certificate replay must pass before any manifest bytes are written.
"""

import argparse
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
import verify

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Write refreshed hashes; otherwise require the existing manifest to be current")
    args = parser.parse_args()
    path = HERE / "manifest.json"
    manifest = verify.load_json(path)
    verify.require(manifest.get("schema_version") == "msc-computation-manifest/1", "Wrong manifest schema")
    verify.require(manifest.get("parameters") == verify.PARAMETERS, "Review mathematical parameter changes explicitly")
    data_path = HERE / manifest["certificate"]["path"]
    report = verify.replay(verify.load_json(data_path))
    manuscript_path = HERE / manifest["manuscript"]["path"]
    manifest["certificate"]["sha256"] = verify.sha256(data_path)
    manifest["manuscript"]["sha256"] = verify.sha256(manuscript_path)
    manifest["expected_summary"] = {key: report[key] for key in
                                    ("cases", "nodes", "leaves", "counts_by_quotient")}
    manifest["script_sha256"] = {name: verify.sha256(HERE / name) for name in verify.SCRIPT_NAMES}
    raw = json.dumps(manifest, indent=2) + "\n"
    if args.write:
        path.write_text(raw, encoding="utf-8")
        status = "MANIFEST_REFRESHED_AFTER_EXACT_REPLAY"
    else:
        verify.require(raw == path.read_text(encoding="utf-8"), "Manifest is stale; review changes before using --write")
        status = "MANIFEST_CURRENT"
    print(json.dumps({"status": status, "manifest_sha256": verify.sha256(path)}, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError) as error:
        print(f"MANIFEST CHECK FAILED: {error}", file=sys.stderr)
        raise SystemExit(1)
