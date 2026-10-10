# Preliminary repair and full verification

The `mathlib-full.yml` dispatch scope defaults to `full`. That path retains the
complete build, strict warning/output gates, and public-theorem axiom audit.

`full-repair` runs the same bounded preliminary repair loop and then **every
normal full verification stage**: API lint, theory warning/output gates,
certificates, metadata, inverse lookups, rows, full theorem, complete Archive
integration, Archive warning/output gates, and the public-theorem axiom audit.
The preliminary phase and all subsequent stages share the existing resource
limits and deadline. No full stage is skipped because the preliminary phase was
clean.

The full-repair report identifies a changed candidate by its baseline commit,
the retained `source.diff` digest, and its source snapshot; it does not label
that candidate as the unmodified baseline commit. Source identity is checked
before each full stage and after the last one. `candidate_full_pass: true` and
`full_verification_performed: true` are emitted only after every full gate passes.
When a patch exists, `all_pass` remains false and
`immutable_source_followup_required` is true until the changes are committed and
an immutable-source run is completed. The report still records that all gates
passed for the exact patched candidate.

If the first full pass reaches the final Archive warning replay and fails only
on exact supported unused-`Infinite K` warnings, full-repair can perform a second
bounded repair phase over the `Archive` target. The full theorem and Archive
normal builds must already have succeeded. Other warnings, compiler errors,
resource failures, or protected-source cases still fail the job.

After successful Archive repair, **every normal full stage is rerun**, starting
with foundations and finishing with the strict Archive warning/output gates and
the public-theorem axiom audit. Those logs use the `final-2-` prefix, preserving
the first-pass diagnostics. The final report identifies the final patched
snapshot and only its final axiom report can produce `candidate_full_pass`.
The Archive repair phase runs at most 20 build/replay passes under the same job
deadline and resource limits; it cannot start a third full pass or suppress a
subsequent failure. Its records are saved separately as `archive-repair.json`.

`theory-repair` is a separate diagnostic operation. It runs the same 134 theory
targets with ordinary `lake --rehash build`, then retrieves all cached warning
logs through `--no-build --wfail`. Both commands use the existing resource guard,
memory limits, worker count, and shared job deadline. A warning-only replay exit
is accepted solely as diagnostic input, not as verification success.

Only exact `linter.unusedSectionVars` warnings listing `[Infinite K]` alone can
produce edits. Each edit inserts `omit [Infinite K] in` before a matched theorem's
documentation, attributes, and modifiers, inside any existing resource-option
wrappers. Existing source bytes are preserved. The parser checks tracked paths,
declaration names/lines, source snapshots, and rejects protected statement files,
symlinks, mixed instance lists, unsupported layouts, and repeated repairs.

The operation has at most 20 compile/replay passes. It stops on compilation or
resource failure, unsupported targeted diagnostics, a changed source snapshot,
or the iteration/deadline bound. It does not build certificates or perform the
final theorem audit. Even a completed diagnostic run reports `all_pass: false`
and `full_verification_performed: false`.

Artifacts include `source.diff`, `theory-repair.json`, `report.json`, and every
guarded build/replay log. Review the diff, commit the intended source changes,
and dispatch `full` on that immutable commit before treating the formalization
as verified. The tool never commits or pushes source changes.

Local regression tests include the full controller flow with stubbed compiler
commands, candidate provenance, and failure gates (no proof-project build):

```sh
python3 -m unittest discover -s .github/scripts/tests -v
```

## Recorded execution and mandatory workflow verdict

The build job records the controller's actual exit code, source identity and
checksummed result artifacts. It may finish cleanly after recording a failed
verification so its cache has an opportunity to persist. This job is explicitly
named as execution/cache retention, not a verification verdict. Cache generation
loss has not been confirmed: consecutive cold mounts motivated this attempt,
but node-local misses and cache lineage are also possible causes. Successful
cache reuse is not assumed or claimed.

The separate mandatory verdict job runs even when the build job fails. It rejects
missing, partial, crashed, corrupt or mismatched reports, failed resources,
missing full stages, incorrect commands and missing or unexpected axioms. It
also checks the recorded source for tracked edits and unexpected Lean files.
There is no workflow-level or job-level `continue-on-error`.

For `full`, the overall workflow passes only for the expected immutable commit
after all 14 full stages and the axiom audit pass. For `full-repair`, a changed
candidate may have passed every gate, but its overall verdict remains failed
until the patch is committed and its immutable-source follow-up passes. An
unchanged full-repair candidate may pass the normal immutable verdict.
`theory-repair` remains diagnostic-only and cannot satisfy a full-verification
verdict. If branch protection is used, require the mandatory verdict job rather
than the cache-execution job alone.
