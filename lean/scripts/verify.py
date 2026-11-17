#!/usr/bin/env python3
"""Record all-module Lean builds, source guards, axiom closure, and kernel replay."""

from __future__ import annotations

import argparse
from datetime import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
from zoneinfo import ZoneInfo

PROJECT = Path(__file__).resolve().parents[1]
REPOSITORY = PROJECT.parent


def timestamp() -> str:
    return datetime.now(ZoneInfo("America/New_York")).isoformat(timespec="seconds")


def capture(*args: str) -> str:
    return subprocess.check_output(args, cwd=PROJECT, text=True).strip()


def without_comments_and_strings(source: str) -> str:
    """Mask nested Lean comments and strings while retaining line numbers."""
    result = list(source)
    i = depth = 0
    string = False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                result[i : i + 2] = "  "
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                result[i : i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if source[i] != "\n":
                    result[i] = " "
                i += 1
        elif string:
            char = source[i]
            if char != "\n":
                result[i] = " "
            if char == "\\" and i + 1 < len(source):
                if source[i + 1] != "\n":
                    result[i + 1] = " "
                i += 2
            else:
                string = char != '"'
                i += 1
        elif source.startswith("/-", i):
            result[i : i + 2] = "  "
            depth = 1
            i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end == -1 else end
            result[i:end] = " " * (end - i)
            i = end
        elif source[i] == '"':
            result[i] = " "
            string = True
            i += 1
        else:
            i += 1
    return "".join(result)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--rebuild-project", action="store_true",
                        help="Invalidate only this project's module traces before the full build")
    parser.add_argument("--skip-kernel-replay", action="store_true",
                        help="Omit the additional leanchecker replay (build/audit checks still run)")
    args = parser.parse_args()
    output = args.output if args.output.is_absolute() else REPOSITORY / args.output
    output.mkdir(parents=True, exist_ok=True)
    report = {
        "status": "running", "started_at": timestamp(),
        "source_commit": capture("git", "rev-parse", "HEAD"),
        "lean_version": capture("lean", "--version"),
        "lake_version": capture("lake", "--version"),
        "toolchain": (PROJECT / "lean-toolchain").read_text().strip(),
        "phases": [],
    }

    def save() -> None:
        (output / "build.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(label: str, command: list[str], extra_env: dict[str, str] | None = None) -> None:
        print(f"Running {label}", flush=True)
        started = time.monotonic()
        logfile = output / f"{label}.log"
        env = os.environ.copy()
        if extra_env:
            env.update(extra_env)
        with logfile.open("w") as log:
            result = subprocess.run(command, cwd=PROJECT, env=env,
                                    stdout=log, stderr=subprocess.STDOUT)
        text = logfile.read_text()
        report["phases"].append({
            "name": label, "working_directory": "lean", "command": command,
            "exit_code": result.returncode,
            "seconds": round(time.monotonic() - started, 3),
            "log": logfile.name,
            "log_sha256": hashlib.sha256(logfile.read_bytes()).hexdigest(),
            "warning_diagnostics": len(re.findall(r"(?m)^warning:", text)),
            "panic_diagnostics": text.count("PANIC at "),
        })
        save()
        if result.returncode:
            raise RuntimeError(f"{label} failed; see {logfile}")
        print(f"Passed {label}", flush=True)

    try:
        files = sorted(p for p in capture("git", "ls-files", "--", "*.lean").splitlines()
                       if p.endswith(".lean"))
        if not files or not all(p.startswith(("GluelumpPerimeterLaw.",
                                             "GluelumpPerimeterLaw/",
                                             "GluelumpPerimeterLawTests.",
                                             "GluelumpPerimeterLawTests/")) for p in files):
            raise RuntimeError("Unexpected or empty tracked Lean source inventory")
        modules = [str(Path(p).with_suffix("")).replace("/", ".") for p in files]
        patterns = {
            "proof_placeholder_or_native_decision": re.compile(r"\b(?:sorry|admit|sorryAx|native_decide)\b"),
            "axiom_or_constant_declaration": re.compile(
                r"(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*(?:axiom|constant)\b"),
            "unsafe_code": re.compile(r"\bunsafe\b"),
        }
        findings = []
        inventory = []
        for path, module in zip(files, modules):
            source = (PROJECT / path).read_text()
            masked = without_comments_and_strings(source)
            for kind, pattern in patterns.items():
                for match in pattern.finditer(masked):
                    findings.append({"file": "lean/" + path, "kind": kind,
                                     "line": masked.count("\n", 0, match.start()) + 1})
            inventory.append({"file": "lean/" + path, "module": module,
                              "source_sha256": hashlib.sha256(source.encode()).hexdigest()})
        report["source_scan"] = {"files_checked": len(files), "findings": findings}
        report["modules"] = inventory
        manifest_bytes = (PROJECT / "lake-manifest.json").read_bytes()
        manifest = json.loads(manifest_bytes)
        report["manifest_sha256"] = hashlib.sha256(manifest_bytes).hexdigest()
        report["dependency_revisions"] = [
            {"name": p["name"], "revision": p.get("rev")}
            for p in manifest["packages"]]
        save()
        if findings:
            raise RuntimeError("Source guard found forbidden constructs")
        lake = ["lake", "--no-cache", "--no-ansi", "build"]
        run("narrow-build", lake + ["GluelumpPerimeterLaw.InfiniteVolumePerimeterLaw"])
        removed = 0
        if args.rebuild_project:
            for module in modules:
                trace = (PROJECT / ".lake/build/lib/lean" /
                         Path(*module.split(".")).with_suffix(".trace"))
                if trace.exists():
                    trace.unlink()
                    removed += 1
        report["project_traces_invalidated"] = removed
        run("all-modules-build", lake + modules)
        for item in inventory:
            artifact = (PROJECT / ".lake/build/lib/lean" /
                        Path(*item["module"].split(".")).with_suffix(".olean"))
            item["olean_sha256"] = hashlib.sha256(artifact.read_bytes()).hexdigest()
        run("regression-build", lake + ["GluelumpPerimeterLawTests"])
        with tempfile.TemporaryDirectory(prefix="gluelump-axiom-audit-") as tmp:
            audit = Path(tmp) / "Audit.lean"
            audit.write_text("".join(f"import {m}\n" for m in modules) +
                             (PROJECT / "scripts/axiom_audit.lean.in").read_text())
            run("compiled-axiom-audit", ["lake", "env", "lean", str(audit)],
                {"GLUELUMP_AUDIT_JSON": str(output / "axioms.json")})
        audit_result = json.loads((output / "axioms.json").read_text())
        report["axiom_audit"] = {k: v for k, v in audit_result.items() if k != "declarations"}
        if not args.skip_kernel_replay:
            run("kernel-replay", ["lake", "env", "leanchecker", "--verbose",
                                  "GluelumpPerimeterLaw", "GluelumpPerimeterLawTests"],
                {"LEAN_NUM_THREADS": "2"})
        report["kernel_replay_performed"] = not args.skip_kernel_replay
        report["status"] = "passed"
        report["finished_at"] = timestamp()
        save()
        print(f"Verified {len(files)} Lean files and "
              f"{audit_result['declarations_checked']} declarations. Record: {output}", flush=True)
        return 0
    except Exception as exc:
        report["status"] = "failed"
        report["finished_at"] = timestamp()
        report["error"] = str(exc)
        save()
        print(exc, file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
