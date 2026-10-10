import ast
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
import froberg_theory_repair as repair


def warning(path, line, name="Froberg.helper", classes=None, direct=False):
    classes = classes or ["[Infinite K]"]
    prefix = f"{path}:{line}:0: warning: " if direct else f"warning: {path}:{line}:0: "
    return (prefix + f"automatically included section variable(s) unused in theorem `{name}`:\n"
            + "".join("  " + value + "\n" for value in classes)
            + "consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n"
            + "  omit [Infinite K] in theorem ...\n\n" + repair.NOTE + "\n")


class Repository(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name).resolve()
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        subprocess.run(["git", "config", "user.email", "test@example.invalid"], cwd=self.root, check=True)
        subprocess.run(["git", "config", "user.name", "Test"], cwd=self.root, check=True)

    def tearDown(self):
        self.temp.cleanup()

    def source(self, text, name="Helper"):
        path = self.root / "Archive/Froberg" / (name + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(text.encode())
        return path

    def commit(self):
        subprocess.run(["git", "add", "."], cwd=self.root, check=True)
        subprocess.run(["git", "commit", "-qm", "fixture"], cwd=self.root, check=True)

    def apply(self, source, declaration="helper"):
        path = self.source(source)
        self.commit()
        line = next(i for i, value in enumerate(source.splitlines(), 1)
                    if "theorem " + declaration in value)
        return path, repair.apply_warnings(self.root, [
            repair.Warning(str(path), line, 0, "Froberg." + declaration)])


class ParseTests(unittest.TestCase):
    def test_singleton_and_direct_formats(self):
        for direct in [False, True]:
            result, unsupported, count = repair.parse_warnings(warning("Archive/Froberg/Helper.lean", 3, direct=direct))
            self.assertEqual(len(result), 1)
            self.assertEqual(count, 1)
            self.assertFalse(unsupported)

    def test_multiple_classes_and_missing_linter_note_fail_closed(self):
        for text in [warning("a.lean", 1, classes=["[Infinite K]", "[Fintype I]"]),
                     warning("a.lean", 1).replace(repair.NOTE, "")]:
            result, unsupported, _ = repair.parse_warnings(text)
            self.assertFalse(result)
            self.assertEqual(len(unsupported), 1)

    def test_other_warnings_are_not_repaired(self):
        result, unsupported, count = repair.parse_warnings(
            warning("a.lean", 1, classes=["[FiniteDimensional K V]"])
            + "warning: a.lean:1:0: unused variable\n")
        self.assertFalse(result)
        self.assertFalse(unsupported)
        self.assertEqual(count, 2)

    def test_duplicates_are_deduplicated(self):
        text = warning("a.lean", 1)
        result, _, _ = repair.parse_warnings(text + text)
        self.assertEqual(len(result), 1)


class InsertionTests(Repository):
    def test_stacked_options_docs_attributes_and_existing_omit(self):
        source = ("namespace Froberg\n"
                  "set_option maxHeartbeats 900000 in -- Keep this budget.\n"
                  "set_option synthInstance.maxHeartbeats 200000 in\n"
                  "omit [Fintype I] in\n"
                  "/-- Nested /- comment -/ documentation. -/\n"
                  "@[simp,\n  grind]\n"
                  "private theorem helper (x : K) : x = x := rfl\n")
        path, records = self.apply(source)
        after = path.read_text()
        self.assertIn("omit [Fintype I] in\nomit [Infinite K] in\n/--", after)
        self.assertEqual(after.replace("omit [Infinite K] in\n", ""), source)
        self.assertEqual(len(records[0]["insertions"]), 1)

    def test_inline_attribute_and_unicode_are_preserved(self):
        source = "namespace Froberg\n/-- α documentation. -/\n@[simp] theorem αhelper : True := by trivial\n"
        path, _ = self.apply(source, "αhelper")
        self.assertEqual(path.read_text().replace("omit [Infinite K] in\n", ""), source)

    def test_section_variable_brackets_are_not_an_attribute(self):
        source = "variable {K : Type*} [Field K] [Infinite K]\n/-- Identity. -/\ntheorem helper : True := by trivial\n"
        path, _ = self.apply(source)
        self.assertIn("[Infinite K]\nomit [Infinite K] in\n/--", path.read_text())

    def test_qualified_and_private_declaration_names(self):
        source = "private theorem Nested.helper : True := by trivial\n"
        path = self.source(source)
        self.commit()
        repair.apply_warnings(self.root, [repair.Warning(
            str(path), 1, 0, "_private.Example.0.Froberg.Nested.helper")])
        self.assertEqual(path.read_text().replace("omit [Infinite K] in\n", ""), source)

    def test_multiple_edits_use_one_snapshot(self):
        source = "theorem helper : True := by trivial\ntheorem caller : True := by trivial\n"
        path = self.source(source)
        self.commit()
        repair.apply_warnings(self.root, [repair.Warning(str(path), 1, 0, "F.helper"),
                                         repair.Warning(str(path), 2, 0, "F.caller")])
        self.assertEqual(path.read_text().replace("omit [Infinite K] in\n", ""), source)

    def test_crlf_and_indentation(self):
        source = "namespace Froberg\r\n  theorem helper : True := by trivial\r\n"
        path, _ = self.apply(source)
        self.assertIn(b"  omit [Infinite K] in\r\n  theorem", path.read_bytes())
        self.assertEqual(path.read_bytes().replace(b"  omit [Infinite K] in\r\n", b""), source.encode())

    def test_rejects_stale_location_inline_wrapper_and_repeat(self):
        for source in ["theorem changed : True := by trivial\n",
                       "set_option maxHeartbeats 100 in theorem helper : True := by trivial\n",
                       "omit [Infinite K] in\ntheorem helper : True := by trivial\n",
                       'def text := "theorem helper : True"\n']:
            path = self.source(source)
            self.commit()
            line = len(source.splitlines())
            with self.assertRaises(repair.RepairError):
                repair.apply_warnings(self.root, [repair.Warning(str(path), line, 0, "F.helper")])
            self.assertEqual(path.read_text(), source)

    def test_rejects_protected_outside_untracked_and_symlink_paths(self):
        protected_paths = [self.source("theorem helper : True := by trivial\n", Path(path).stem)
                           for path in repair.PROTECTED]
        protected = protected_paths[0]
        self.commit()
        untracked = self.source("theorem helper : True := by trivial\n", "Untracked")
        link = self.root / "Archive/Froberg/Link.lean"
        link.symlink_to(protected)
        for path in [*protected_paths, untracked, link, self.root / "../Outside.lean"]:
            with self.assertRaises((repair.RepairError, subprocess.SubprocessError)):
                repair.apply_warnings(self.root, [repair.Warning(str(path), 1, 0, "F.helper")])


class LoopTests(Repository):
    def test_two_module_cascade_remains_diagnostic_only(self):
        first = self.source("theorem helper : True := by trivial\n", "First")
        second = self.source("theorem caller : True := by trivial\n", "Second")
        self.commit()
        logs = self.root / "logs"
        logs.mkdir()
        calls = []

        def execute(stage, command):
            calls.append(command)
            text = ""
            if stage.endswith("warnings"):
                if "omit" not in first.read_text():
                    text = warning(str(first), 1)
                elif "omit" not in second.read_text():
                    text = warning(str(second), 1, "Froberg.caller")
            code = 1 if text else 0
            (logs / (stage + ".log")).write_text(text)
            return {"stage": stage, "returncode": code, "resource": {"exit_status": code}}

        code = repair.run_repair(self.root, logs, {"commit": "fixture"}, ["Archive.Froberg.First"],
                                 execute, lambda info, rc: info["exit_status"] == rc, lambda: 1000)
        report = json.loads((logs / "report.json").read_text())
        self.assertEqual(code, 0)
        self.assertEqual(len(report["iterations"]), 3)
        self.assertFalse(report["all_pass"])
        self.assertTrue(report["diagnostic_only"])
        self.assertFalse(report["full_verification_performed"])
        self.assertIn("+omit [Infinite K] in", (logs / "source.diff").read_text())
        self.assertTrue(all(command[-1] == "Archive.Froberg.First" for command in calls))

    def test_bound_does_not_apply_an_unverified_last_edit(self):
        path = self.source("theorem helper : True := by trivial\n")
        self.commit()
        logs = self.root / "logs"
        logs.mkdir()

        def execute(stage, command):
            text = warning(str(path), 1) if stage.endswith("warnings") else ""
            (logs / (stage + ".log")).write_text(text)
            return {"stage": stage, "returncode": int(bool(text)), "resource": {}}

        code = repair.run_repair(self.root, logs, {}, ["Archive.Froberg.Helper"], execute,
                                 lambda *_: True, lambda: 1000, max_iterations=1)
        self.assertEqual(code, 1)
        self.assertNotIn("omit", path.read_text())
        self.assertFalse(json.loads((logs / "report.json").read_text())["all_pass"])

    def test_replay_error_and_external_source_change_stop_without_repair(self):
        for mutate in [False, True]:
            path = self.source("theorem helper : True := by trivial\n", "Changing")
            self.commit()
            logs = self.root / ("changed-logs" if mutate else "error-logs")
            logs.mkdir()

            def execute(stage, command):
                text = ""
                if stage.endswith("warnings"):
                    text = warning(str(path), 1)
                    if mutate:
                        path.write_text(path.read_text() + "-- changed externally\n")
                    else:
                        text += str(path) + ":1:0: error(lean.typeMismatch): failure\n"
                (logs / (stage + ".log")).write_text(text)
                return {"stage": stage, "returncode": int(bool(text)), "resource": {}}

            code = repair.run_repair(self.root, logs, {}, ["Archive.Froberg.Changing"], execute,
                                     lambda *_: True, lambda: 1000)
            self.assertEqual(code, 1)
            self.assertNotIn("omit", path.read_text())
            self.assertFalse(json.loads((logs / "report.json").read_text())["all_pass"])

    def test_resource_failure_and_deadline_stop(self):
        self.source("theorem helper : True := by trivial\n")
        self.commit()
        for timed_out in [False, True]:
            logs = self.root / ("deadline" if timed_out else "resource")
            logs.mkdir()
            called = []

            def execute(stage, command):
                called.append(stage)
                return {"stage": stage, "returncode": 0, "resource": {}}

            code = repair.run_repair(self.root, logs, {}, ["Archive.Froberg.Helper"], execute,
                                     lambda *_: False, lambda: 0 if timed_out else 1000)
            self.assertEqual(code, 1)
            self.assertEqual(len(called), 0 if timed_out else 1)
            self.assertFalse(json.loads((logs / "report.json").read_text())["all_pass"])

    def test_deadline_after_replay_does_not_apply(self):
        path = self.source("theorem helper : True := by trivial\n")
        self.commit()
        logs = self.root / "late-interruption"
        logs.mkdir()
        time_left = [1000]

        def execute(stage, command):
            text = warning(str(path), 1) if stage.endswith("warnings") else ""
            (logs / (stage + ".log")).write_text(text)
            if text:
                time_left[0] = 0
            return {"stage": stage, "returncode": int(bool(text)), "resource": {}}

        code = repair.run_repair(self.root, logs, {}, ["Archive.Froberg.Helper"], execute,
                                 lambda *_: True, lambda: time_left[0])
        self.assertEqual(code, 1)
        self.assertNotIn("omit", path.read_text())


class FullModeRegression(unittest.TestCase):
    def test_full_stage_commands_and_guard_are_unchanged(self):
        path = ".github/scripts/ci_mathlib_build.py"
        root = SCRIPTS.parents[1]
        before = ast.parse(subprocess.check_output(["git", "show", "HEAD:" + path], cwd=root, text=True))
        after = ast.parse((root / path).read_text())

        def assignment(tree, name):
            return next(n.value for n in ast.walk(tree) if isinstance(n, ast.Assign)
                        and any(isinstance(t, ast.Name) and t.id == name for t in n.targets))

        for name in ["stages", "base", "foundation_base", "limits", "end"]:
            self.assertEqual(ast.dump(assignment(before, name)), ast.dump(assignment(after, name)))
        for name in ["guarded_command", "choose_bootstrap"]:
            old = next(n for n in ast.walk(before) if isinstance(n, ast.FunctionDef) and n.name == name)
            new = next(n for n in ast.walk(after) if isinstance(n, ast.FunctionDef) and n.name == name)
            self.assertEqual(ast.dump(old), ast.dump(new))


if __name__ == "__main__":
    unittest.main()
