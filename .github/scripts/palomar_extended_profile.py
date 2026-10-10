#!/usr/bin/env python3
"""Custom twelve-hour preflight resources; the pinned verifier stays unchanged."""
import argparse
import copy
import hashlib
import importlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import uuid

PIPELINE_COMMIT = "d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44"
PROFILE = "palomar-namespace-32x64-12h-v1"
LABEL = "nscloud-ubuntu-24.04-amd64-32x64-with-features"
WORKERS = 16
OPTIONS = {"comparator_config_path": "comparator.json",
           "authorization_relationship": "I am a responsible author or maintainer"}


def verify_pipeline(root):
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    if head != PIPELINE_COMMIT:
        raise ValueError("The custom preflight requires the exact pinned pipeline commit")
    changed = subprocess.check_output(["git", "diff", "--name-only", "HEAD", "--"],
                                      cwd=root, text=True).splitlines()
    if set(changed) - {"execution-profiles.json"}:
        raise ValueError("Only the local execution-profile catalogue may differ from the pin")


def extend_catalogue(root):
    path = root / "execution-profiles.json"
    data = json.loads(path.read_text())
    original = data["profiles"]["palomar-namespace-16x32-v1"]
    for identifier, cores, memory in [("palomar-namespace-16x32-12h-v1", 16, 32),
                                       (PROFILE, 32, 64)]:
        selected = copy.deepcopy(original)
        label = f"nscloud-ubuntu-24.04-amd64-{cores}x{memory}-with-features"
        selected["runner"]["label"] = label
        selected["runner"]["labels"] = [label, "namespace-features:container.privileged=true"]
        selected["limits"].update(job_timeout_minutes=720, execution_budget_seconds=43200,
                                  minimum_host_memory_bytes=(28 if memory == 32 else 56) * 1024**3)
        data["profiles"][identifier] = selected
    path.write_text(json.dumps(data, indent=2) + "\n")


def modules(root):
    sys.path.insert(0, str(root))
    return (importlib.import_module("scripts.verification_profile"),
            importlib.import_module("scripts.workflow_report"))


def validate_inputs(root, inputs, *, output=None):
    """Exercise the pinned intake, catalogue, and finalizer before expensive work."""
    value = dict(inputs)
    if value.get("pipeline_commit") != PIPELINE_COMMIT:
        raise ValueError("Unexpected pipeline revision")
    if value.get("execution_profile") != PROFILE or value.get("mode") != "full":
        raise ValueError("This workflow is the custom 64 GB full preflight only")
    if value.get("repository") != "Vlado-V/froberg-2d":
        raise ValueError("Unexpected submission repository")
    if not re.fullmatch(r"[0-9a-f]{40}", str(value.get("commit", ""))):
        raise ValueError("The submission commit must be forty lowercase hex characters")
    if json.loads(value.get("options", "{}")) != OPTIONS:
        raise ValueError("The comparator path and authorization scope must remain unchanged")
    attempt = value.get("execution_attempt") or uuid.uuid4().hex
    if not re.fullmatch(r"[0-9a-f]{32}", attempt):
        raise ValueError("execution_attempt must contain exactly 32 lowercase hex characters")
    value["execution_attempt"] = attempt
    profile_module, finalizer = modules(root)
    intake = importlib.import_module("scripts.submission_contract")
    _, identifier = intake.submission_request({"inputs": value})
    profile = profile_module.load_profile(PROFILE)
    if (profile["runner"]["label"] != LABEL or profile["limits"]["job_timeout_minutes"] != 720
            or profile["limits"]["execution_budget_seconds"] != 43200
            or profile["limits"]["minimum_host_memory_bytes"] != 56 * 1024**3
            or profile["limits"]["memory_high_percent"] != 95
            or profile["limits"]["memory_max_percent"] != 98):
        raise ValueError("Resolved custom profile has unexpected resource settings")
    fixture = {"schema_version": 1, "source": {"repository": value["repository"],
               "commit": value["commit"]}, "submission": {"submission_id": identifier},
               "status": "error", "errors": ["early parser fixture"], "diagnostics": []}
    checked = finalizer.finalize(fixture, value, {}, workflow_url="https://example.invalid/preflight")
    if checked["execution_attempt"] != attempt or checked["execution_profile"] != PROFILE:
        raise ValueError("Pinned finalizer did not preserve normalized identifiers")
    if output:
        with output.open("a") as handle:
            handle.write("inputs_json=" + json.dumps(value, separators=(",", ":")) + "\n")
            handle.write("execution_attempt=" + attempt + "\n")
    return value


def check_runner(root, disk_path):
    profile_module, _ = modules(root)
    profile = profile_module.load_profile(PROFILE)
    observed = profile_module.check_host(profile, disk_path)
    if observed["effective_cpus"] < 32 or len(os.sched_getaffinity(0)) < WORKERS:
        raise ValueError("The custom preflight requires the authorized 32-CPU/64-GB machine")
    facts = {"custom_preflight": True, "official_acceptance": False,
             "pipeline_commit": PIPELINE_COMMIT, "execution_profile": PROFILE,
             "observed_host": observed, "worker_cpu_affinity": WORKERS,
             "con_ron_jobs": 2, "execution_budget_seconds": 43200,
             "job_timeout_minutes": 720,
             "pinned_script_sha256": {name: hashlib.sha256((root / "scripts" / name).read_bytes()).hexdigest()
                 for name in ["verify_submission.py", "workflow_report.py", "verification_profile.py",
                              "supervise_cgroup.py"]}}
    print(json.dumps(facts, indent=2))
    return facts


def run_capped(command):
    if not command:
        raise ValueError("Missing command for the CPU-capped verifier")
    cpus = sorted(os.sched_getaffinity(0))
    if len(cpus) < WORKERS:
        raise ValueError("Fewer than sixteen available CPUs")
    os.sched_setaffinity(0, set(cpus[:WORKERS]))
    os.execvp(command[0], command)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("--validate-inputs", action="store_true")
    parser.add_argument("--github-output", type=Path)
    parser.add_argument("--check-runner", type=Path)
    parser.add_argument("--provenance-output", type=Path)
    parser.add_argument("--run-capped", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    root = args.root.resolve()
    verify_pipeline(root)
    extend_catalogue(root)
    if args.validate_inputs:
        validate_inputs(root, json.loads(os.environ["PALOMAR_INPUTS"]), output=args.github_output)
        print("Pinned intake/profile/finalizer input checks passed before execution.")
    if args.check_runner:
        facts = check_runner(root, args.check_runner)
        if args.provenance_output:
            args.provenance_output.write_text(json.dumps(facts, indent=2) + "\n")
    if args.run_capped is not None:
        run_capped(args.run_capped)
    if not (args.validate_inputs or args.check_runner or args.run_capped is not None):
        print("Custom profiles installed: unchanged verifier, 720-minute job, 43200-second budget.")


if __name__ == "__main__":
    main()
