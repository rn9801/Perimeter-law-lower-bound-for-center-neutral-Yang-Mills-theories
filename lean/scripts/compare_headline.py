#!/usr/bin/env python3
"""Run pinned Lean Comparator on the real headline and a separate paper contract."""

import argparse
from datetime import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
from zoneinfo import ZoneInfo

PROJECT = Path(__file__).resolve().parents[1]
REPOSITORY = PROJECT.parent
COMPARATOR_REVISION = "1cfc5d8ad183bf65efe7accd0efc175b6b8f25b6"
EXPORT_REVISION = "a3e35a584f59b390667db7269cd37fca8575e4bf"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def revision(path: Path) -> str:
    return subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"],
                                   text=True).strip()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--comparator-root", required=True, type=Path)
    parser.add_argument("--landrun", required=True, type=Path)
    parser.add_argument("--landrun-source", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    output = args.output if args.output.is_absolute() else REPOSITORY / args.output
    output.mkdir(parents=True, exist_ok=True)
    comparator_root = args.comparator_root.resolve()
    comparator = comparator_root / ".lake/build/bin/comparator"
    export_root = comparator_root / ".lake/packages/lean4export"
    exporter = export_root / ".lake/build/bin/lean4export"
    landrun = args.landrun.resolve()
    record = {"status": "running", "source_commit": revision(REPOSITORY),
              "started_at": datetime.now(ZoneInfo("America/New_York")).isoformat(),
              "runs": []}

    def save() -> None:
        (output / "comparator.json").write_text(json.dumps(record, indent=2) + "\n")

    def run(label: str, command: list[str], cwd: Path, env: dict[str, str]) -> tuple[int, str]:
        print(f"Running {label}", flush=True)
        start = time.monotonic()
        log_path = output / f"{label}.log"
        with log_path.open("w") as log:
            process = subprocess.run(command, cwd=cwd, env=env,
                                     stdout=log, stderr=subprocess.STDOUT)
        record["runs"].append({"name": label, "command": command,
                               "exit_code": process.returncode,
                               "seconds": round(time.monotonic() - start, 3),
                               "log": log_path.name, "log_sha256": digest(log_path)})
        save()
        return process.returncode, log_path.read_text()

    try:
        if revision(comparator_root) != COMPARATOR_REVISION:
            raise RuntimeError("Use the pinned Comparator v4.30.0 revision")
        if revision(export_root) != EXPORT_REVISION:
            raise RuntimeError("Unexpected lean4export revision")
        for binary in [comparator, exporter, landrun]:
            if not os.access(binary, os.X_OK):
                raise RuntimeError(f"Missing executable: {binary}")
        record["tools"] = {
            "comparator_revision": COMPARATOR_REVISION,
            "lean4export_revision": EXPORT_REVISION,
            "comparator_sha256": digest(comparator),
            "lean4export_sha256": digest(exporter),
            "landrun_sha256": digest(landrun),
            "landrun_revision": revision(args.landrun_source) if args.landrun_source else None,
        }
        templates = PROJECT / "verification/comparator"
        record["inputs"] = {
            p.name: digest(p) for p in sorted(templates.iterdir())
            if p.is_file() and (p.name.endswith(".lean.in") or p.name == "config.json")
        }
        record["configuration"] = json.loads((templates / "config.json").read_text())
        record["unix_socket_restriction"] = "seccomp denies AF_UNIX socket/socketpair in parent and children"
        record["landrun_cli_adapter_sha256"] = digest(PROJECT / "scripts/landrun_compat.py")
        record["seccomp_launcher_sha256"] = digest(PROJECT / "scripts/no_unix_sockets.py")
        with tempfile.TemporaryDirectory(prefix="gluelump-headline-comparator-") as directory:
            fixture = Path(directory)
            for name in ["GluelumpPerimeterLaw", "GluelumpPerimeterLaw.lean",
                         "GluelumpPerimeterLawTests", "GluelumpPerimeterLawTests.lean"]:
                (fixture / name).symlink_to(PROJECT / name, target_is_directory=(PROJECT / name).is_dir())
            for name in ["lake-manifest.json", "lean-toolchain"]:
                shutil.copy2(PROJECT / name, fixture / name)
            fixture_config = (PROJECT / "lakefile.toml").read_text()
            for name in ["Spec", "Challenge", "Solution", "Mismatch"]:
                fixture_config += f'\n[[lean_lib]]\nname = "{name}"\n'
                shutil.copyfile(templates / f"{name}.lean.in", fixture / f"{name}.lean")
            (fixture / "lakefile.toml").write_text(fixture_config)
            (fixture / ".lake").mkdir()
            (fixture / ".lake/packages").symlink_to(PROJECT / ".lake/packages", target_is_directory=True)
            shutil.copytree(PROJECT / ".lake/build", fixture / ".lake/build")
            config = record["configuration"]
            (fixture / "config.json").write_text(json.dumps(config, indent=2) + "\n")
            negative = {**config, "challenge_module": "Mismatch"}
            (fixture / "mismatch.json").write_text(json.dumps(negative, indent=2) + "\n")
            env = os.environ.copy()
            env["COMPARATOR_LANDRUN"] = str(PROJECT / "scripts/landrun_compat.py")
            env["GLUELUMP_LANDRUN_BINARY"] = str(landrun)
            env["COMPARATOR_LEAN4EXPORT"] = str(exporter)
            # Each fixture is trusted test code and contains complete proofs.
            # Prebuilding is permitted by Comparator and avoids changing dependency caches.
            code, _ = run("comparator-fixture-build",
                          ["lake", "--no-cache", "--no-ansi", "build",
                           "Spec", "Challenge", "Solution", "Mismatch"], fixture, env)
            if code:
                raise RuntimeError("Comparator fixture did not compile")
            launcher = PROJECT / "scripts/no_unix_sockets.py"
            command = ["lake", "env", "python3", str(launcher), str(comparator)]
            code, text = run("headline-comparator", command + ["config.json"], fixture, env)
            if code or "Your solution is okay!" not in text:
                raise RuntimeError("Headline Comparator check failed")
            code, text = run("comparator-negative-control", command + ["mismatch.json"], fixture, env)
            if code == 0 or "theorem statement do not match" not in text:
                raise RuntimeError("Comparator did not reject the changed-statement control")
        record["status"] = "passed"
        record["negative_control"] = "changed statement rejected as expected"
        record["finished_at"] = datetime.now(ZoneInfo("America/New_York")).isoformat()
        save()
        print(f"Headline Comparator passed and changed-statement control rejected. Record: {output}", flush=True)
        return 0
    except Exception as error:
        record["status"] = "failed"
        record["error"] = str(error)
        save()
        print(error, file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
