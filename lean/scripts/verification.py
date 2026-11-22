#!/usr/bin/env python3
"""Shared environment and file checks for the pinned MSC formalization."""

from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
LEAN_VERSION = "4.37.0-rc1"
LEAN_COMMIT = "0b77e12952ad39077d80d8bd6b66d601f225c321"
MATHLIB_COMMIT = "c47f9ad906c5ec32a953f99911b446cd26dcc123"
TARGETS = (
    ("CubeSections.maximalSectionVolume", "CubeSections.UpperBoundStatement"),
    ("CubeSections.balancedSectionAttains", "CubeSections.AttainmentStatement"),
    ("CubeSections.maximalSectionVolume_eq_iff", "CubeSections.EqualityStatement"),
    ("CubeSections.maximalSections_main", "CubeSections.MainStatement"),
)
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def fingerprint(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def check_targets(project=ROOT):
    manifest = json.loads((project / "target_manifest.json").read_text())
    stated = tuple((item["declaration"], item["contract"]) for item in manifest["mandatory_targets"])
    if stated != TARGETS or set(manifest["allowed_axioms"]) != ALLOWED_AXIOMS:
        raise ValueError("The four public targets and permitted axioms do not match the fixed contract.")
    return manifest


def environment(lean_bin=None, packages=None, project=ROOT):
    project = Path(project).resolve()
    env = {key: value for key, value in os.environ.items() if not key.startswith("LEAN_")}
    env["GIT_OPTIONAL_LOCKS"] = "0"
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    if lean_bin is None:
        executable = shutil.which("lean")
        if executable is None:
            raise RuntimeError("Lean is not on PATH. Install the pinned toolchain or pass --lean-bin PATH.")
        runtime = Path(subprocess.check_output([executable, "--print-prefix"], cwd=project,
                                              env=env, text=True).strip()).resolve()
        lean = runtime / "bin/lean"
    else:
        lean = Path(lean_bin).resolve() / "lean"
        runtime = lean.parent.parent
    version = subprocess.check_output([str(lean), "--version"], cwd=project,
                                      env=env, text=True).strip()
    if f"version {LEAN_VERSION}," not in version or LEAN_COMMIT not in version:
        raise RuntimeError("Wrong Lean version or commit: " + version)
    if (project / "lean-toolchain").read_text().strip() != f"leanprover/lean4:v{LEAN_VERSION}":
        raise RuntimeError("lean-toolchain does not match the fixed version.")
    packages = Path(packages).resolve() if packages is not None else project / ".lake/packages"
    manifest = json.loads((project / "lake-manifest.json").read_text())
    if next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib") != MATHLIB_COMMIT:
        raise RuntimeError("The Mathlib revision in lake-manifest.json has changed.")
    roots = [project / ".lake/build/lib/lean"]
    revisions = {}
    for package in manifest["packages"]:
        checkout = packages / package["name"]
        if not checkout.is_dir():
            raise RuntimeError(f"Missing dependency {checkout}; populate the pinned Lake packages first.")
        head = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"],
                                       env=env, text=True).strip()
        if head != package["rev"]:
            raise RuntimeError("Wrong dependency revision: " + package["name"])
        subprocess.run(["git", "-C", str(checkout), "diff", "--quiet", "HEAD", "--"],
                       env=env, check=True)
        untracked = subprocess.check_output(["git", "-C", str(checkout), "ls-files", "--others",
                                            "--exclude-standard"], env=env, text=True)
        if untracked.strip():
            raise RuntimeError("Dependency checkout has untracked nonignored files: " + package["name"])
        cache = checkout / ".lake/build/lib/lean"
        if cache.is_dir():
            if (cache / "CubeSections.olean").exists() or (cache / "CubeSections").exists():
                raise RuntimeError("A dependency cache shadows the project namespace.")
            roots.append(cache)
        revisions[package["name"]] = head
    core = runtime / "lib/lean"
    identity = {"lean_version": version, "lean_binary_sha256": sha(lean),
                "toolchain_file_sha256": sha(project / "lean-toolchain"),
                "lake_manifest_sha256": sha(project / "lake-manifest.json"),
                "lakefile_sha256": sha(project / "lakefile.toml"),
                "package_revisions": revisions}
    library = core / "libleanshared.so"
    if library.is_file():
        identity["lean_shared_library_sha256"] = sha(library)
    env["LEAN_PATH"] = os.pathsep.join(map(str, roots))
    env["LEAN_SYSROOT"] = str(runtime)
    env["LEAN_ABORT_ON_PANIC"] = "1"
    env["PATH"] = str(runtime / "bin") + os.pathsep + env.get("PATH", "")
    return lean, env, identity, roots + [core]


def uncomment(text):
    """Blank nested Lean comments and strings, retaining line breaks for import parsing."""
    result = []
    index = depth = 0
    string = False
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                depth += 1; result.extend("  "); index += 2
            elif text.startswith("-/", index):
                depth -= 1; result.extend("  "); index += 2
            else:
                result.append("\n" if text[index] == "\n" else " "); index += 1
        elif string:
            if text[index] == "\\" and index + 1 < len(text):
                result.extend("  "); index += 2
            elif text[index] == '"':
                string = False; result.append(" "); index += 1
            else:
                result.append("\n" if text[index] == "\n" else " "); index += 1
        elif text.startswith("/-", index):
            depth = 1; result.extend("  "); index += 2
        elif text.startswith("--", index):
            end = text.find("\n", index)
            end = len(text) if end < 0 else end
            result.extend(" " * (end - index)); index = end
        elif text[index] == '"':
            string = True; result.append(" "); index += 1
        else:
            result.append(text[index]); index += 1
    if depth or string:
        raise ValueError("Unclosed Lean comment/string while scanning imports")
    return "".join(result)


def imports(path):
    result = []
    for line in uncomment(Path(path).read_text()).splitlines():
        if re.match(r"^\s*(?:public\s+|meta\s+)?import\b", line):
            match = re.fullmatch(r"\s*import\s+([A-Za-z0-9_.]+)\s*", line)
            if not match:
                raise ValueError(f"Unsupported import syntax in {path}: {line.strip()}")
            result.append(match.group(1))
    return result


def is_local(module):
    return module == "CubeSections" or module.startswith("CubeSections.")


def module_path(module, suffix=".lean"):
    return Path(module.replace(".", "/") + suffix)


def cached_result_matches(receipt, expected, output):
    """A cache hit binds current inputs and the actual output to one successful compilation."""
    return (receipt.get("schema") == "msc-build-module/1"
            and receipt.get("exit_code") == 0
            and receipt.get("source_unchanged") is True
            and receipt.get("inputs_unchanged") is True
            and receipt.get("inputs") == expected
            and Path(output).is_file()
            and receipt.get("output_sha256") == sha(output))
