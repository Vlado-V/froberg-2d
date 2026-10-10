import copy
import importlib.util
import json
import os
from pathlib import Path
from types import SimpleNamespace
import subprocess
import tempfile
import unittest
from unittest.mock import patch

BASE = Path(__file__).resolve().parents[3]
CONTROLLER = BASE
spec = importlib.util.spec_from_file_location("ci_mathlib_result", CONTROLLER / ".github/scripts/ci_mathlib_result.py")
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


class VerdictTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.logs = Path(self.temp.name).resolve()
        self.commit = "a" * 40
        self.root = Path("/fixed/mathlib")
        self.scope = "full"
        self.resource = {"state": "finished", "exit_status": 0, "placement_ok": True,
                         "launch_error": None, "term_signal": None, "deadline_fired": False,
                         "liveness_lost": False, "populated_after_kill": False,
                         "limits_applied": {key: True for key in ["memory.high", "memory.max",
                             "memory.swap.max", "memory.oom.group", "pids.max"]}}
        self.report = {"source": {"repository": "Vlado-V/mathlib4", "commit": self.commit,
                                  "toolchain": "leanprover/lean4:v4.35.0-rc4"},
                       "all_pass": True, "stages": [],
                       "axioms": {name: ["propext"] for name in [
                           "Froberg.paperStatement", "Froberg.uniformMainStatement"]}}
        for name, command in mod.expected_stages(CONTROLLER, self.root):
            self.report["stages"].append({"stage": name, "command": command, "returncode": 0,
                                          "resource": copy.deepcopy(self.resource)})
            self.write(name + "-resource.json", self.resource)
            (self.logs / (name + ".log")).write_text("")
        (self.logs / "axiom-audit.log").write_text(
            "PASS: main theorem dependencies use only propext, Classical.choice, Quot.sound\n"
            "Froberg.paperStatement depends on axioms: [propext]\n"
            "Froberg.uniformMainStatement depends on axioms: [propext]\n")
        self.write("capacity.json", {"effective_memory_bytes": 64 * 1024**3,
            "limits": {"memory.high": 56 * 1024**3, "memory.max": 60 * 1024**3,
                       "memory.swap.max": 0, "memory.oom.group": 1, "pids.max": 8192},
            "lake_threads": 16})
        self.write("guard-preflight.json", {"attempts": [{"returncode": 0, "status": self.resource}]})
        (self.logs / "tracked-source.diff").write_bytes(b"")
        self.execution = {"schema": 1, "scope": "full", "expected_commit": self.commit,
                          "run_id": "123", "run_attempt": "1", "controller_commit": "b" * 40,
                          "source_head": self.commit, "source_root": str(self.root),
                          "completed": True, "controller_exit": 0, "unexpected_lean_sources": []}
        self.save()

    def tearDown(self):
        self.temp.cleanup()

    def write(self, name, value):
        (self.logs / name).write_text(json.dumps(value))

    def save(self):
        self.write("report.json", self.report)
        self.execution["artifacts"] = {p.name: {"bytes": p.stat().st_size, "sha256": mod.digest(p)}
                                       for p in self.logs.iterdir() if p.name != "execution.json"}
        self.write("execution.json", self.execution)

    def validate(self):
        return mod.validate(self.logs, CONTROLLER, self.commit, self.scope, "123", "1", "b" * 40)

    def rejected(self):
        self.save()
        with self.assertRaises((mod.InvalidResult, OSError)):
            self.validate()

    def test_valid_full(self):
        self.assertTrue(self.validate()["verified"])

    def full_repair(self):
        self.scope = self.execution["scope"] = "full-repair"
        self.report.update(mode="full-repair", candidate_full_pass=True,
                           full_verification_performed=True, immutable_source_followup_required=False)
        self.report["source"].update(baseline_commit=self.commit,
            candidate={"committed": True, "kind": "immutable-commit",
                       "patch_sha256": mod.hashlib.sha256(b"").hexdigest()})
        (self.logs / "source.diff").write_bytes(b"")

    def test_valid_unchanged_full_repair(self):
        self.full_repair(); self.save()
        self.assertTrue(self.validate()["verified"])

    def test_partial_or_false_report(self):
        self.report["all_pass"] = False; self.rejected()

    def test_crash_or_nonzero_exit(self):
        self.execution["controller_exit"] = -9; self.rejected()

    def test_false_is_not_exit_zero(self):
        self.execution["controller_exit"] = False; self.rejected()

    def test_incomplete_capture(self):
        self.execution["completed"] = False; self.rejected()

    def test_wrong_run_identity(self):
        self.execution["run_id"] = "old"; self.rejected()

    def test_wrong_source_identity(self):
        self.report["source"]["commit"] = "c" * 40; self.rejected()

    def test_corrupted_artifact(self):
        (self.logs / "theory.log").write_text("changed after sealing")
        with self.assertRaises(mod.InvalidResult): self.validate()

    def test_missing_report(self):
        (self.logs / "report.json").unlink()
        with self.assertRaises(mod.InvalidResult): self.validate()

    def test_missing_full_stage(self):
        self.report["stages"].pop(4); self.rejected()

    def test_wrong_command_cannot_skip_wfail(self):
        self.report["stages"][3]["command"].remove("--wfail"); self.rejected()

    def test_wrong_order(self):
        self.report["stages"][1:3] = list(reversed(self.report["stages"][1:3])); self.rejected()

    def test_bad_resource(self):
        self.report["stages"][5]["resource"]["deadline_fired"] = True
        self.write("large-certificates-resource.json", self.report["stages"][5]["resource"])
        self.rejected()

    def test_unapplied_resource_limit(self):
        self.report["stages"][5]["resource"]["limits_applied"]["memory.max"] = False
        self.write("large-certificates-resource.json", self.report["stages"][5]["resource"])
        self.rejected()

    def test_resource_json_mismatch(self):
        bad = copy.deepcopy(self.resource); bad["exit_status"] = 1
        self.write("archive-warnings-resource.json", bad); self.rejected()

    def test_bad_capacity(self):
        cap = json.loads((self.logs / "capacity.json").read_text()); cap["lake_threads"] = 32
        self.write("capacity.json", cap); self.rejected()

    def test_bad_axioms(self):
        (self.logs / "axiom-audit.log").write_text(
            "PASS: main theorem dependencies use only propext, Classical.choice, Quot.sound\n"
            "Froberg.paperStatement depends on axioms: [sorryAx]\n"
            "Froberg.uniformMainStatement depends on axioms: [propext]\n")
        self.rejected()

    def test_missing_axiom_pass(self):
        (self.logs / "axiom-audit.log").write_text(""); self.rejected()

    def test_uncommitted_full_repair(self):
        self.full_repair(); self.report["source"]["candidate"]["committed"] = False
        self.rejected()

    def test_tracked_diff_rejected_even_if_report_claims_immutable(self):
        (self.logs / "tracked-source.diff").write_text("+ changed proof")
        self.rejected()

    def test_unexpected_lean_source(self):
        self.execution["unexpected_lean_sources"] = ["AddedProof.lean"]; self.rejected()

    def test_diagnostic_is_not_verification(self):
        self.scope = self.execution["scope"] = "theory-repair"; self.rejected()

    def test_duplicate_json_rejected(self):
        self.save(); (self.logs / "execution.json").write_text('{"schema":1,"schema":1}')
        with self.assertRaises(mod.InvalidResult): self.validate()

    def test_capture_records_failure_without_claiming_verification(self):
        args = SimpleNamespace(root=self.logs / "source", logs=self.logs, controller=CONTROLLER,
                               guard=self.logs / "guard", job_start=1, scope="full")
        env = {"SOURCE_COMMIT": self.commit, "GITHUB_RUN_ID": "123", "GITHUB_RUN_ATTEMPT": "1",
               "GITHUB_SHA": "b" * 40}
        with patch.dict(os.environ, env), patch.object(mod.subprocess, "run",
             return_value=subprocess.CompletedProcess([], 7)) as child, patch.object(
             mod.subprocess, "check_output", side_effect=[self.commit + "\n", b"", ""]):
            self.assertEqual(mod.capture(args), 0)
            self.assertIn("ci_mathlib_build.py", child.call_args.args[0][1])
        with self.assertRaises(mod.InvalidResult): self.validate()

    def test_capture_rejects_ignored_untracked_lean_source(self):
        args = SimpleNamespace(root=self.logs / "source", logs=self.logs, controller=CONTROLLER,
                               guard=self.logs / "guard", job_start=1, scope="full")
        env = {"SOURCE_COMMIT": self.commit, "GITHUB_RUN_ID": "123", "GITHUB_RUN_ATTEMPT": "1",
               "GITHUB_SHA": "b" * 40}
        with patch.dict(os.environ, env), patch.object(mod.subprocess, "run",
             return_value=subprocess.CompletedProcess([], 0)), patch.object(
             mod.subprocess, "check_output", side_effect=[self.commit + "\n", b"", "IgnoredProof.lean\n"]
             ) as git:
            self.assertEqual(mod.capture(args), 0)
            self.assertNotIn("--exclude-standard", git.call_args_list[-1].args[0])
        with self.assertRaises(mod.InvalidResult): self.validate()


if __name__ == "__main__":
    unittest.main()
