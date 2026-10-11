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
and `Quot.sound`. The quadratic argument works in every characteristic without
finite base-case rank certificates or external certificate data.

## Registry interface

`Challenge.lean` is the small independent statement specification required by
Palomar. Its one deliberate `sorry` specifies what the registry must check; it
is never imported by the proof. `Solution.lean` proves that same declaration
from the complete development. `comparator.json` also lists all 15 independent
statement definitions for comparison.

## Source layout

- `Froberg/`: the general-degree construction, uniform arithmetic, and conclusion.
- `Quartic/`: the quadratic argument in arbitrary characteristic.
- `OAI/`: the reused polynomial equidistribution lemmas, with source attribution.
- `formalization.yaml`: mathematical scope, provenance, and automation disclosure.

The general-degree construction does not induct on generating degree.
The quadratic case uses a uniform defect recurrence in every characteristic.

`Audit.lean` checks the axiom dependencies of the submitted
`FrobergPaper.main_result` and the loaded local theorem interfaces, allowing only
the three permitted Lean axioms. Palomar verification is pending.

## License and credit

The proof code is licensed under Apache-2.0; see `LICENSE`.
Vlado Vojdanovski is the project author and responsible maintainer. The
formalization was substantially produced using OpenAI Codex agents, as disclosed
in `formalization.yaml`. Reused OAI source attribution and its original license
are retained in `OAI/`. The accompanying manuscript is distributed with the
author's permission and is not covered by the code license.
