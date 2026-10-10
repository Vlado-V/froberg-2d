"""Diagnostic-only repair of exact unusedSectionVars [Infinite K] warnings.

This never certifies a theorem. It only inserts a scoped ``omit`` command; a
separate immutable-source full run is required after review and commit.
"""
from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
import re
import stat
import subprocess


class RepairError(RuntimeError):
    pass


@dataclass(frozen=True)
class Warning:
    path: str
    line: int
    column: int
    declaration: str


HEADER = re.compile(
    r"^(?:warning: (?P<lake>.+?\.lean):(?P<ll>\d+):(?P<lc>\d+): "
    r"|(?P<direct>.+?\.lean):(?P<dl>\d+):(?P<dc>\d+): warning: )"
    r"(?P<message>[^\n\r]*)", re.M)
SECTION = re.compile(
    r"automatically included section variable\(s\) unused in theorem `([^`]+)`:")
NOTE = "Note: This linter can be disabled with `set_option linter.unusedSectionVars false`"
PROTECTED = {"Archive/Froberg/" + name + ".lean" for name in (
    "QuotientModel", "UniformEndToEndAssembly", "Statement", "IndependentStatementBridge",
    "UniformStatement", "IndependentStatement", "HilbertSeries", "UniformMain")}


def parse_warnings(log):
    """Return exact repair targets, unsupported Infinite warnings, and total warnings."""
    headers = list(HEADER.finditer(log))
    targets, unsupported = [], []
    for index, header in enumerate(headers):
        match = SECTION.fullmatch(header["message"])
        if not match:
            continue
        stop = headers[index + 1].start() if index + 1 < len(headers) else len(log)
        block = log[header.end():stop].lstrip("\r\n")
        classes = []
        for line in block.splitlines():
            if re.fullmatch(r"  \[[^\r\n]+\]", line):
                classes.append(line.strip())
            else:
                break
        if "[Infinite K]" not in classes:
            continue
        warning = Warning(header["lake"] or header["direct"],
                          int(header["ll"] or header["dl"]),
                          int(header["lc"] or header["dc"]), match[1])
        if classes != ["[Infinite K]"] or NOTE not in block:
            unsupported.append({**asdict(warning), "classes": classes,
                                "reason": "Only the exact singleton linter warning is supported"})
        else:
            targets.append(warning)
    return list(dict.fromkeys(targets)), unsupported, len(headers)


@dataclass(frozen=True)
class Token:
    kind: str
    value: str
    start: int
    end: int


def tokens(source):
    """Small lexical scanner; comments and strings cannot impersonate declarations."""
    result, i, size = [], 0, len(source)
    while i < size:
        start = i
        if source[i].isspace():
            i += 1
            continue
        if source.startswith("--", i):
            end = source.find("\n", i)
            i = size if end < 0 else end
            kind = "comment"
        elif source.startswith("/-", i):
            depth, i = 1, i + 2
            while i < size and depth:
                if source.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                raise RepairError("Unterminated block comment")
            kind = "comment"
        elif (raw := re.match(r'r(#+)"', source[i:])):
            marker = '"' + raw[1]
            end = source.find(marker, i + raw.end())
            if end < 0:
                raise RepairError("Unterminated raw string")
            i, kind = end + len(marker), "string"
        elif source[i] == '"':
            i += 1
            while i < size:
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise RepairError("Unterminated string")
            kind = "string"
        elif source[i] == "«":
            end = source.find("»", i + 1)
            if end < 0:
                raise RepairError("Unterminated quoted identifier")
            i, kind = end + 1, "identifier"
        elif source[i].isalpha() or source[i] == "_":
            i += 1
            while i < size and (source[i].isalnum() or source[i] in "_'!?₀₁₂₃₄₅₆₇₈₉"):
                i += 1
            kind = "identifier"
        else:
            i, kind = i + 1, "symbol"
        result.append(Token(kind, source[start:i], start, i))
    return result


def insertion(source, warning):
    lines = source.splitlines(keepends=True)
    if not 1 <= warning.line <= len(lines):
        raise RepairError("Warning line is outside the current source")
    line_start = sum(map(len, lines[:warning.line - 1]))
    line_end = line_start + len(lines[warning.line - 1])
    ts = tokens(source)
    matches = []
    for i, token in enumerate(ts[:-1]):
        if token.value not in {"theorem", "lemma"} or not line_start <= token.start < line_end:
            continue
        name = ts[i + 1]
        declared = name.value.removeprefix("«").removesuffix("»")
        cursor = i + 2
        while (cursor + 1 < len(ts) and ts[cursor].value == "." and
               ts[cursor + 1].kind == "identifier"):
            declared += "." + ts[cursor + 1].value
            cursor += 2
        if name.kind == "identifier" and (warning.declaration == declared or
                                           warning.declaration.endswith("." + declared)):
            matches.append(i)
    if len(matches) != 1:
        raise RepairError("Warning declaration does not uniquely match the current source line")
    index = matches[0]
    # Walk only declaration prefixes, stopping at the `in` of a scoped option/omit.
    while index:
        previous = ts[index - 1]
        if previous.value in {"private", "protected", "noncomputable", "unsafe", "partial", "public"}:
            index -= 1
        elif previous.kind == "comment":
            start = source.rfind("\n", 0, previous.start) + 1
            if source[start:previous.start].strip():
                break  # A trailing option comment belongs to the outer wrapper.
            index -= 1
        elif previous.value == "]":
            depth, cursor = 1, index - 2
            while cursor >= 0 and depth:
                depth += (ts[cursor].value == "]") - (ts[cursor].value == "[")
                cursor -= 1
            if depth or cursor < 0 or ts[cursor].value != "@":
                break  # For example, the end of a preceding `variable [...]` command.
            index = cursor
        else:
            break
    start = source.rfind("\n", 0, ts[index].start) + 1
    indent = source[start:ts[index].start]
    if indent.strip():
        raise RepairError("Inline declaration/wrapper layout is unsupported")
    # Repeated warnings from an already-repaired command indicate stale/mismatched logs.
    prefix = source[max(0, start - 600):start]
    if re.search(r"omit[^\n]*(?:\n[ \t]+[^\n]*){0,6}\[Infinite K\][^\n]* in\s*$", prefix):
        raise RepairError("Declaration already has an Infinite omission")
    newline = "\r\n" if "\r\n" in source else "\n"
    return start, indent + "omit [Infinite K] in" + newline


def resolve_path(root, raw):
    path = Path(raw)
    if ".." in path.parts:
        raise RepairError("Parent path traversal is unsupported")
    path = path if path.is_absolute() else root / path
    try:
        relative = path.relative_to(root).as_posix()
    except ValueError as exc:
        raise RepairError("Warning path is outside the source checkout") from exc
    if relative in PROTECTED or not re.fullmatch(
            r"Archive/Froberg/(?:[A-Za-z_][A-Za-z0-9_]*/)*[A-Za-z_][A-Za-z0-9_]*\.lean", relative):
        raise RepairError("Warning path is not an editable internal Archive module")
    if path.resolve() != path or not path.is_file():
        raise RepairError("Symlink or missing source path")
    subprocess.run(["git", "ls-files", "--error-unmatch", relative], cwd=root,
                   check=True, capture_output=True)
    return path, relative


def apply_warnings(root, warnings):
    plans = {}
    for warning in warnings:
        path, relative = resolve_path(root, warning.path)
        if path not in plans:
            original = path.read_bytes()
            plans[path] = [relative, original, original.decode("utf-8"), {}]
        _, _, source, edits = plans[path]
        offset, text = insertion(source, warning)
        if offset in edits and edits[offset][0] != text:
            raise RepairError("Conflicting insertions")
        edits[offset] = (text, asdict(warning))
    prepared = []
    for path, (relative, original, source, edits) in plans.items():
        result = source
        for offset, (text, _) in sorted(edits.items(), reverse=True):
            result = result[:offset] + text + result[offset:]
        prepared.append((path, original, result.encode("utf-8"), {
            "path": relative, "before_sha256": hashlib.sha256(original).hexdigest(),
            "after_sha256": hashlib.sha256(result.encode("utf-8")).hexdigest(),
            "insertions": [{"offset": offset, "text": text, "warning": warning}
                           for offset, (text, warning) in sorted(edits.items())]}))
    if any(path.read_bytes() != before for path, before, _, _ in prepared):
        raise RepairError("Source changed while planning repairs")
    for path, _, after, _ in prepared:
        temporary = path.with_suffix(".lean.theory-repair-tmp")
        temporary.write_bytes(after)
        temporary.chmod(stat.S_IMODE(path.stat().st_mode))
        temporary.replace(path)
    return [record for _, _, _, record in prepared]


def atomic_json(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def source_snapshot(root):
    result = {}
    paths = subprocess.check_output(
        ["git", "ls-files", "-z", "--", "Archive/Froberg"], cwd=root).decode().split("\0")
    for relative in paths:
        if not relative.endswith(".lean"):
            continue
        path = root / relative
        if path.is_symlink() or not path.is_file():
            raise RepairError("Tracked Lean source is missing or a symlink")
        result[relative] = hashlib.sha256(path.read_bytes()).hexdigest()
    return result


def run_repair(root, logs, source, targets, execute, resource_finished, remaining,
               max_iterations=20, standalone=True):
    """Run guarded normal builds/replays; always publish a diagnostic-only result."""
    if not 1 <= max_iterations <= 20:
        raise RepairError("Repair iteration bound must be between 1 and 20")
    report = {"mode": "theory-repair", "diagnostic_only": True, "all_pass": False,
              "full_verification_performed": False, "full_verification_required": True,
              "source": source, "theory_target_count": len(targets),
              "max_iterations": max_iterations, "iterations": [], "status": "running"}

    def publish():
        diff = subprocess.check_output(
            ["git", "diff", "--no-ext-diff", "--no-color", "HEAD", "--", "Archive/Froberg"],
            cwd=root)
        (logs / "source.diff").write_bytes(diff)
        report["source_changed"] = bool(diff)
        atomic_json(logs / "theory-repair.json", report)
        if standalone:
            atomic_json(logs / "report.json", report)

    code = 1
    try:
        subprocess.run(["git", "diff", "--quiet", "HEAD", "--"], cwd=root, check=True)
        untracked = subprocess.check_output(
            ["git", "ls-files", "--others", "--exclude-standard", "--", "Archive/Froberg"],
            cwd=root).decode().splitlines()
        if any(path.endswith(".lean") for path in untracked):
            raise RepairError("Untracked Archive Lean source is not a fixed input")
        publish()
        for iteration in range(1, max_iterations + 1):
            if remaining() <= 30:
                raise RepairError("Shared job deadline reached")
            snapshot = source_snapshot(root)
            entry = {"iteration": iteration, "edits": []}
            entry["source_snapshot_sha256"] = hashlib.sha256(
                json.dumps(snapshot, sort_keys=True).encode()).hexdigest()
            report["iterations"].append(entry)
            build = execute(f"theory-repair-{iteration:02}-build",
                            ["lake", "--rehash", "--no-ansi", "build", *targets])
            entry["build"] = build
            if build["returncode"] != 0 or not resource_finished(build["resource"], 0):
                raise RepairError("Normal theory build or its resource guard failed")
            # --wfail forces all cached warning logs to be replayed. Its warning
            # exit is diagnostic data here, never a verification acceptance.
            replay = execute(f"theory-repair-{iteration:02}-warnings",
                             ["lake", "--no-ansi", "build", "--no-build", "--wfail", *targets])
            entry["replay"] = replay
            rc = replay["returncode"]
            if rc not in {0, 1} or not resource_finished(replay["resource"], rc):
                raise RepairError("Warning replay or its resource guard failed")
            log = (logs / (replay["stage"] + ".log")).read_text()
            errors = re.findall(r"^error(?:\([^\n)]*\))?: (.*)$", log, re.M)
            if any(error != "build failed" for error in errors) or re.search(
                    r"^.+\.lean:\d+:\d+: error(?:\([^\n)]*\))?:", log, re.M):
                raise RepairError("Warning replay contains a compiler error")
            if source_snapshot(root) != snapshot:
                raise RepairError("Archive source changed while building or replaying diagnostics")
            warnings, unsupported, total = parse_warnings(log)
            entry.update(targeted_warnings=[asdict(w) for w in warnings],
                         unsupported_warnings=unsupported, total_warning_count=total)
            if rc == 1 and not total:
                raise RepairError("Warning replay failed without recognized warnings")
            if unsupported:
                raise RepairError("Unsupported Infinite warning; no speculative repair performed")
            if not warnings:
                report["status"], code = "no_targeted_warnings", 0
                break
            if iteration == max_iterations:
                raise RepairError("Iteration bound reached with targeted warnings remaining")
            if remaining() <= 30:
                raise RepairError("Shared job deadline or interruption reached before editing")
            entry["edits"] = apply_warnings(root, warnings)
            publish()
    except (RepairError, OSError, ValueError, subprocess.SubprocessError) as exc:
        report.update(status="stopped", reason=str(exc))
    except SystemExit as exc:
        report.update(status="interrupted_or_deadline", reason=str(exc))
        code = exc.code if isinstance(exc.code, int) and exc.code else 1
    finally:
        publish()
    if standalone:
        print("DIAGNOSTIC ONLY: " + report["status"] +
              "; review source.diff and run full immutable-source verification.", flush=True)
    else:
        print("PRELIMINARY REPAIR: " + report["status"] +
              "; full verification follows only if this phase succeeded.", flush=True)
    return code


def candidate_identity(root, baseline):
    """Identify the exact tracked candidate as baseline plus a retained patch."""
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    if head != baseline["commit"]:
        raise RepairError("Candidate baseline commit changed")
    untracked = subprocess.check_output(
        ["git", "ls-files", "--others", "--", "Archive/Froberg"], cwd=root).decode().splitlines()
    if any(path.endswith(".lean") for path in untracked):
        raise RepairError("Untracked Archive Lean source changed the candidate")
    diff = subprocess.check_output(
        ["git", "diff", "--no-ext-diff", "--no-color", "HEAD", "--"], cwd=root)
    archive_diff = subprocess.check_output(
        ["git", "diff", "--no-ext-diff", "--no-color", "HEAD", "--", "Archive/Froberg"],
        cwd=root)
    if diff != archive_diff:
        raise RepairError("Candidate has tracked changes outside Archive/Froberg")
    snapshot = source_snapshot(root)
    metadata = {key: value for key, value in baseline.items() if key != "commit"}
    metadata["baseline_commit"] = baseline["commit"]
    if not diff:
        metadata["commit"] = baseline["commit"]
    metadata["candidate"] = {
        "kind": "baseline-plus-patch" if diff else "immutable-commit",
        "committed": not bool(diff),
        "patch_artifact": "source.diff",
        "patch_sha256": hashlib.sha256(diff).hexdigest(),
        "archive_source_snapshot_sha256": hashlib.sha256(
            json.dumps(snapshot, sort_keys=True).encode()).hexdigest(),
    }
    return metadata, diff


def record_candidate(root, logs, baseline):
    metadata, diff = candidate_identity(root, baseline)
    (logs / "source.diff").write_bytes(diff)
    atomic_json(logs / "candidate-source.json", metadata)
    return metadata


def verify_candidate_unchanged(root, baseline, expected):
    metadata, _ = candidate_identity(root, baseline)
    if metadata != expected:
        raise RepairError("Candidate source changed during the full verification stages")
