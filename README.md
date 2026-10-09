# Fröberg through degree 2d

This development proves Theorem 1.1 of Vlado Vojdanovski's accompanying paper:
for every positive generating degree `d`, there is a variable threshold that
works simultaneously for every infinite field and every number of generators.
The generic quotient has Fröberg's predicted Hilbert function through degree `2d`.

The public theorem is `Froberg.uniformMainStatement` in
`Froberg/UniformMain.lean`. The same conclusion is stated independently using
only Mathlib in `Froberg/IndependentStatement.lean` and proved as
`Froberg.paperStatement`. The two statements are definitionally equivalent.

## Verify

Install the pinned Lean toolchain with Elan, then run:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The project pins Lean 4.35.0-rc3 and its Mathlib dependency. Every mathematical
proof is checked by Lean; the permitted axioms are `propext`, `Classical.choice`,
and `Quot.sound`. The certificate loader only constructs literal data and proof
terms. It does not certify ranks by trusting an external numerical result.

The finite quadratic certificates for dimensions 28, 29, and 30 are included.
Their inverse matrices use ordinary Git files in ordered chunks. Sparse rows
are reconstructed from the included generator coefficients and monomial
metadata by Lean's elaboration-time code. The existing proof-producing checker
then checks the inverse equations and their polynomial interpretation. No
network access or separate certificate generator is needed during compilation.
The row-check modules form eight dependency chains and start after the large
arithmetic stages. The profile and sharp arithmetic stages each use eight
parallel modules. Each compiler process uses one thread and elaborates theorem
proofs sequentially. The profile stage contains 728 smaller kernel checks with
the same 26 public conclusions. These choices balance parallel compilation
with memory use during a fresh build.
If certificate inputs change, rebuild from a fresh project `.lake/build`
directory because Lake does not track the elaborators' binary file reads.

## Registry interface

`Challenge.lean` is the small independent statement specification required by
Palomar. Its one deliberate `sorry` specifies what the registry must check; it
is never imported by the proof. `Solution.lean` proves that same declaration
from the complete development. `comparator.json` also lists all 15 independent
statement definitions for comparison.

## Source layout

- `Froberg/`: the general-degree construction, uniform arithmetic, and conclusion.
- `Quartic/`: the quadratic argument and checked finite certificates.
- `OAI/`: the reused polynomial equidistribution lemmas, with source attribution.
- `certificates/finite/`: data for the three initial characteristic-two dimensions.
- `formalization.yaml`: mathematical scope, provenance, and automation disclosure.

The general-degree construction does not induct on generating degree.
The characteristic-two quadratic case uses a three-variable induction from
dimensions 28, 29, and 30.

`Audit.lean` checks the axiom dependencies of the submitted
`FrobergPaper.main_result` and the loaded local theorem interfaces, allowing only
the three permitted Lean axioms. Palomar verification is pending.

## License and credit

The proof code and certificate data are licensed under Apache-2.0; see `LICENSE`.
Vlado Vojdanovski is the project author and responsible maintainer. The
formalization was substantially produced using OpenAI Codex agents, as disclosed
in `formalization.yaml`. Reused OAI source attribution and its original license
are retained in `OAI/`. The accompanying manuscript is distributed with the
author's permission and is not covered by the code license.
