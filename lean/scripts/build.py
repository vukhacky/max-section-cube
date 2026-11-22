#!/usr/bin/env python3
"""Build the MSC import closure with pinned dependencies and verified cache receipts.

This never downloads, edits or rebuilds dependency packages. Use --fresh to
compile every project module; otherwise only fully matching receipts are reused.
"""

from pathlib import Path
import argparse
import datetime
import fcntl
import json
import subprocess
import sys
import time

from verification import (ROOT, cached_result_matches, check_targets, environment,
                          fingerprint, imports, is_local, module_path, sha, write_json)


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path, help="Directory containing the pinned lean executable")
    parser.add_argument("--packages", type=Path, help="Pinned packages directory; default .lake/packages")
    parser.add_argument("--fresh", action="store_true", help="Compile all project modules, ignoring receipts")
    parser.add_argument("--timeout", type=int, default=600, help="Seconds per compiler invocation")
    parser.add_argument("--memory", type=int, default=6144, help="Compiler memory limit in MiB")
    args = parser.parse_args()
    check_targets()
    lean, env, identity, roots = environment(args.lean_bin, args.packages)
    output_root = ROOT / ".lake/build/lib/lean"
    evidence = ROOT / ".lake/verification"
    evidence.mkdir(parents=True, exist_ok=True)
    with (evidence / "build.lock").open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise RuntimeError("Another verification build is using this project.")
        order, seen, visiting, direct = [], set(), set(), {}
        def visit(module):
            if module in seen:
                return
            if module in visiting:
                raise ValueError("Local import cycle at " + module)
            visiting.add(module)
            direct[module] = imports(ROOT / module_path(module))
            for dependency in direct[module]:
                if is_local(dependency):
                    visit(dependency)
            visiting.remove(module)
            seen.add(module)
            order.append(module)
        visit("CubeSections")
        write_json(evidence / "import_graph.json", {"order": order, "imports": direct})
        compiler_arguments = ["-j1", f"-M{args.memory}"]
        context = fingerprint({"environment": identity, "compiler_arguments": compiler_arguments,
                               "builder_sha256": sha(Path(__file__)),
                               "helper_sha256": sha(Path(__file__).with_name("verification.py"))})
        summary = {"schema": "msc-build/1", "started_utc": utc(), "fresh_requested": args.fresh,
                   "environment": identity, "modules": [], "status": "RUNNING"}
        tick = time.monotonic()
        fingerprints = {}
        code = 0
        for number, module in enumerate(order, 1):
            source = ROOT / module_path(module)
            output = output_root / module_path(module, ".olean")
            receipt_path = evidence / "modules" / module_path(module, ".json")
            output.parent.mkdir(parents=True, exist_ok=True)
            dependencies, dependency_paths = {}, {}
            for dependency in direct[module]:
                candidates = [root / module_path(dependency, ".olean") for root in roots]
                matches = [candidate for candidate in candidates if candidate.is_file()]
                if len(matches) != 1:
                    raise RuntimeError(f"Expected one object for import {dependency}; found {len(matches)}")
                dependency_paths[dependency] = matches[0]
                dependencies[dependency] = {"output_sha256": sha(matches[0])}
                if is_local(dependency):
                    dependencies[dependency]["input_fingerprint"] = fingerprints[dependency]
            expected = {"source_sha256": sha(source), "dependencies": dependencies,
                        "compiler_context": context}
            previous = json.loads(receipt_path.read_text()) if receipt_path.is_file() else {}
            if not args.fresh and cached_result_matches(previous, expected, output):
                fingerprints[module] = fingerprint(expected)
                summary["modules"].append({"module": module, "action": "verified_reuse", "exit_code": 0})
                print(f"{number}/{len(order)} REUSE {module}", flush=True)
                continue
            temporary = output.with_name(output.stem + ".building.olean")
            if temporary.exists():
                temporary.unlink()
            command = [str(lean), *compiler_arguments, "-o", str(temporary), str(source)]
            started, begin = utc(), time.monotonic()
            try:
                run = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                     capture_output=True, timeout=args.timeout)
                code, log = run.returncode, run.stdout + run.stderr
            except subprocess.TimeoutExpired as error:
                def decode(value):
                    return value.decode(errors="replace") if isinstance(value, bytes) else value or ""
                code, log = 124, decode(error.stdout) + decode(error.stderr) + "\nMODULE_TIMEOUT\n"
            unchanged = sha(source) == expected["source_sha256"]
            imports_unchanged = all(sha(dependency_paths[dep]) == record["output_sha256"]
                                    for dep, record in dependencies.items())
            if not unchanged or not imports_unchanged:
                code = 98
                log += "\nCOMPILATION_INPUT_CHANGED\n"
            if code == 0 and not temporary.is_file():
                code = 97
                log += "\nCOMPILER_OUTPUT_MISSING\n"
            if code == 0:
                temporary.replace(output)
            elif temporary.exists():
                temporary.unlink()
            entry = {"schema": "msc-build-module/1", "module": module,
                     "source": str(source.relative_to(ROOT)), "inputs": expected,
                     "source_unchanged": unchanged, "inputs_unchanged": imports_unchanged,
                     "started_utc": started, "completed_utc": utc(),
                     "seconds": time.monotonic() - begin, "exit_code": code,
                     "output_sha256": sha(output) if code == 0 else None,
                     "compiler_arguments": compiler_arguments}
            write_json(receipt_path, entry)
            receipt_path.with_suffix(".log").write_text(log)
            summary["modules"].append({"module": module, "action": "compiled", "exit_code": code,
                                       "receipt": str(receipt_path.relative_to(evidence))})
            write_json(evidence / "build.json", summary)
            print(f"{number}/{len(order)} BUILD {module}: exit {code}; {entry['seconds']:.2f}s", flush=True)
            if code:
                break
            fingerprints[module] = fingerprint(expected)
        summary.update({"status": "PASS" if not code else "FAILED_OR_INCOMPLETE", "exit_code": code,
                        "completed_utc": utc(), "seconds": time.monotonic() - tick})
        write_json(evidence / "build.json", summary)
        return code


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"Verification build error: {error}", file=sys.stderr)
        raise SystemExit(1)
