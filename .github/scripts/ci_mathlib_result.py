"""Separate cache-producing execution from the mandatory full-verification verdict.

The build controller and its proof/resource gates are not modified. A failed
controller invocation is recorded as data; only the independent verdict may
declare verification success.
"""
import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


class InvalidResult(RuntimeError):
    pass


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as stream:
        while block := stream.read(1024 * 1024):
            result.update(block)
    return result.hexdigest()


def atomic_json(path, value):
    temp = path.with_suffix(path.suffix + ".tmp")
    temp.write_text(json.dumps(value, indent=2) + "\n")
    temp.replace(path)


def no_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise InvalidResult("Duplicate JSON key: " + key)
        result[key] = value
    return result


def read_json(path):
    if path.stat().st_size > 32 * 1024 * 1024:
        raise InvalidResult("Oversized result JSON")
    return json.loads(path.read_text(), object_pairs_hook=no_duplicate_keys)


def regular_file(root, relative):
    relative = Path(relative)
    if relative.is_absolute() or ".." in relative.parts:
        raise InvalidResult("Invalid artifact path")
    path = root / relative
    if path.resolve() != path or not path.is_file():
        raise InvalidResult("Missing or symlinked artifact: " + str(relative))
    return path


def resource_ok(resource, keys):
    return (resource.get("state") == "finished" and type(resource.get("exit_status")) is int
            and resource.get("exit_status") == 0
            and resource.get("placement_ok") is True
            and not any(resource.get(key) for key in (
                "launch_error", "term_signal", "deadline_fired", "liveness_lost",
                "populated_after_kill"))
            and all(resource.get("limits_applied", {}).get(key) is True for key in keys))


def expected_stages(controller, source_root):
    """Read stage commands from the trusted, unchanged controller source."""
    path = controller / ".github/scripts/ci_mathlib_build.py"
    tree = ast.parse(path.read_text())
    names = {"base", "foundation_base", "q", "theory_targets", "stages"}
    nodes = [node for node in tree.body if isinstance(node, ast.Assign)
             and any(isinstance(target, ast.Name) and target.id in names
                     for target in node.targets)]
    context = {"Path": Path, "__file__": str(path),
               "api_lint": source_root / "FrobergApiDeclarationLint.lean",
               "audit": source_root / "FrobergAxiomAudit.lean"}
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(path), "exec"), context)
    appends = [node for node in tree.body if isinstance(node, ast.Expr)
               and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute)
               and isinstance(node.value.func.value, ast.Name)
               and node.value.func.value.id == "stages" and node.value.func.attr == "append"]
    if len(appends) != 1:
        raise InvalidResult("Unexpected controller stage construction")
    exec(compile(ast.Module(body=appends, type_ignores=[]), str(path), "exec"), context)
    if len(context["stages"]) != 14:
        raise InvalidResult("Unexpected full stage count")
    return context["stages"]


def capture(args):
    """Return cleanly only after recording the actual controller exit and source state."""
    root, logs, controller = args.root.resolve(), args.logs.resolve(), args.controller.resolve()
    logs.mkdir(parents=True, exist_ok=True)
    result = {"schema": 1, "completed": False, "scope": args.scope,
              "expected_commit": os.environ["SOURCE_COMMIT"],
              "run_id": os.environ["GITHUB_RUN_ID"],
              "run_attempt": os.environ["GITHUB_RUN_ATTEMPT"],
              "controller_commit": os.environ["GITHUB_SHA"],
              "source_root": str(root), "started_epoch": time.time()}
    command = [sys.executable, str(controller / ".github/scripts/ci_mathlib_build.py"),
               "--root", str(root), "--guard", str(args.guard.resolve()),
               "--logs", str(logs), "--job-start", str(args.job_start), "--scope", args.scope]
    result["command"] = command
    try:
        child = subprocess.run(command)
        result["controller_exit"] = child.returncode
        result["source_head"] = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
        (logs / "tracked-source.diff").write_bytes(subprocess.check_output(
            ["git", "diff", "--binary", "--no-ext-diff", "HEAD", "--"], cwd=root))
        untracked = subprocess.check_output(
            ["git", "ls-files", "--others"], cwd=root, text=True).splitlines()
        allowed = {"FrobergApiDeclarationLint.lean", "FrobergAxiomAudit.lean"}
        result["unexpected_lean_sources"] = [path for path in untracked
            if path.endswith(".lean") and path not in allowed and not path.startswith(".lake/")]
        result["completed"] = True
    except (OSError, subprocess.SubprocessError) as error:
        result["recording_error"] = str(error)
    result["finished_epoch"] = time.time()
    manifest = {}
    for path in sorted(logs.rglob("*")):
        if path.is_symlink():
            raise InvalidResult("Symlinked result artifact")
        if path.is_file() and path.name != "execution.json":
            manifest[path.relative_to(logs).as_posix()] = {"bytes": path.stat().st_size,
                                                        "sha256": digest(path)}
    result["artifacts"] = manifest
    atomic_json(logs / "execution.json", result)
    print(f"Build execution recorded: controller_exit={result.get('controller_exit')}, "
          f"completed={result['completed']}; the mandatory verdict determines verification status.",
          flush=True)
    # This is a cache-producing execution job, deliberately not a verification verdict.
    return 0


def validate(logs, controller, expected_commit, scope, run_id, run_attempt, controller_commit):
    logs, controller = logs.resolve(), controller.resolve()
    execution = read_json(regular_file(logs, "execution.json"))
    identity = {"schema": 1, "scope": scope, "expected_commit": expected_commit,
                "run_id": run_id, "run_attempt": run_attempt,
                "controller_commit": controller_commit, "source_head": expected_commit}
    if scope not in {"full", "full-repair"}:
        raise InvalidResult("A diagnostic-only run is not a full verification pass")
    if type(execution.get("schema")) is not int:
        raise InvalidResult("Invalid result schema")
    if any(execution.get(key) != value for key, value in identity.items()):
        raise InvalidResult("Result identity does not match this workflow invocation")
    if (execution.get("completed") is not True or type(execution.get("controller_exit")) is not int
            or execution.get("controller_exit") != 0):
        raise InvalidResult("Controller failed, crashed, or did not finish")
    if execution.get("recording_error") or execution.get("unexpected_lean_sources") != []:
        raise InvalidResult("Source recording failed or found unexpected Lean sources")
    manifest = execution.get("artifacts")
    if not isinstance(manifest, dict):
        raise InvalidResult("Missing artifact manifest")
    for name, entry in manifest.items():
        path = regular_file(logs, name)
        if path.stat().st_size != entry.get("bytes") or digest(path) != entry.get("sha256"):
            raise InvalidResult("Changed or truncated result artifact: " + name)

    def artifact(name):
        if name not in manifest:
            raise InvalidResult("Unrecorded required artifact: " + name)
        return regular_file(logs, name)

    if artifact("tracked-source.diff").read_bytes():
        raise InvalidResult("Repaired/uncommitted source requires an immutable follow-up")
    report = read_json(artifact("report.json"))
    if scope == "full" and report.get("mode", "full") != "full":
        raise InvalidResult("Report mode differs from the requested full run")
    source = report.get("source", {})
    if (report.get("all_pass") is not True or source.get("commit") != expected_commit
            or source.get("repository") != "Vlado-V/mathlib4"
            or source.get("toolchain") != "leanprover/lean4:v4.35.0-rc4"):
        raise InvalidResult("Final immutable-source pass is absent")
    if scope == "full-repair":
        candidate = source.get("candidate", {})
        if (report.get("mode") != "full-repair" or report.get("candidate_full_pass") is not True
                or report.get("full_verification_performed") is not True
                or report.get("immutable_source_followup_required") is not False
                or source.get("baseline_commit") != expected_commit
                or candidate.get("committed") is not True
                or candidate.get("kind") != "immutable-commit"
                or candidate.get("patch_sha256") != hashlib.sha256(b"").hexdigest()
                or artifact("source.diff").read_bytes()):
            raise InvalidResult("Candidate provenance is incomplete or not immutable")

    capacity = read_json(artifact("capacity.json"))
    memory = capacity.get("effective_memory_bytes", 0)
    keys = {"memory.high", "memory.max", "memory.swap.max", "memory.oom.group", "pids.max"}
    limits = {"memory.high": min(56 * 1024**3, int(memory * .90)),
              "memory.max": min(60 * 1024**3, int(memory * .96)), "memory.swap.max": 0,
              "memory.oom.group": 1, "pids.max": 8192}
    if memory < 56 * 1024**3 or capacity.get("limits") != limits or capacity.get("lake_threads") != 16:
        raise InvalidResult("Resource capacity/limits differ from the controller")
    preflight = read_json(artifact("guard-preflight.json"))
    if not any(attempt.get("returncode") == 0 and resource_ok(attempt.get("status", {}), keys)
               for attempt in preflight.get("attempts", [])):
        raise InvalidResult("Missing successful resource preflight")

    expected = expected_stages(controller, Path(execution["source_root"]))
    stages = report.get("stages")
    if not isinstance(stages, list) or len(stages) < len(expected):
        raise InvalidResult("Incomplete final stage list")
    full_passes = report.get("full_passes", 1)
    if type(full_passes) is not int or full_passes not in {1, 2}:
        raise InvalidResult("Unexpected full-pass count")
    prefix = "" if full_passes == 1 else "final-2-"
    for record, (name, command) in zip(stages[-len(expected):], expected):
        name = prefix + name
        resource = read_json(artifact(name + "-resource.json"))
        artifact(name + ".log")
        if (record.get("stage") != name or record.get("command") != command
                or type(record.get("returncode")) is not int or record.get("returncode") != 0
                or record.get("resource") != resource
                or not resource_ok(resource, keys)):
            raise InvalidResult("Incomplete or failed full gate: " + name)

    text = artifact(prefix + "axiom-audit.log").read_text()
    if "PASS: main theorem dependencies use only propext, Classical.choice, Quot.sound" not in text:
        raise InvalidResult("Missing final axiom audit pass")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for theorem in ["Froberg.paperStatement", "Froberg.uniformMainStatement"]:
        match = re.search(re.escape(theorem) + r"['\"]?\s+depends on axioms:\s*\[(.*?)\]", text, re.S)
        if match:
            used = {name.strip() for name in match[1].split(",") if name.strip()}
        elif re.search(re.escape(theorem) + r"['\"]?\s+does not depend on any axioms", text):
            used = set()
        else:
            raise InvalidResult("Missing final axiom report")
        if not used <= allowed or report.get("axioms", {}).get(theorem) != sorted(used):
            raise InvalidResult("Bad or inconsistent final axiom report")
    return {"verified": True, "source_commit": expected_commit, "scope": scope,
            "full_gates": len(expected), "run_id": run_id, "run_attempt": run_attempt}


def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="mode", required=True)
    record = sub.add_parser("capture")
    for name in ["root", "controller", "guard", "logs"]:
        record.add_argument("--" + name, type=Path, required=True)
    record.add_argument("--job-start", type=float, required=True)
    record.add_argument("--scope", choices=["full", "full-repair", "theory-repair"], required=True)
    verdict = sub.add_parser("verdict")
    verdict.add_argument("--logs", type=Path, required=True)
    verdict.add_argument("--controller", type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.mode == "capture":
            return capture(args)
        result = validate(args.logs, args.controller, os.environ["SOURCE_COMMIT"],
                          os.environ["VERIFY_SCOPE"] or "full", os.environ["GITHUB_RUN_ID"],
                          os.environ["GITHUB_RUN_ATTEMPT"], os.environ["GITHUB_SHA"])
        print("PASS: immutable full verification verdict " + json.dumps(result))
        return 0
    except (InvalidResult, OSError, ValueError, KeyError, TypeError, AttributeError) as error:
        print("FAIL: full verification verdict: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
