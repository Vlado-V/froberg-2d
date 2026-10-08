# Fröberg through degree 2d

[Paper](Froberg_through_degree_2d.pdf) and complete Lean formalization.

The main theorem is `Froberg.mainStatement` in
[`Froberg/EndToEndAssembly.lean`](Froberg/EndToEndAssembly.lean).
Its statement is defined in [`Froberg/Statement.lean`](Froberg/Statement.lean).

## Download and verify

Install [Git LFS](https://git-lfs.com/) and
[Lean via Elan](https://lean-lang.org/install/), then run:

```sh
git lfs install
git clone https://github.com/Vlado-V/froberg-2d.git
cd froberg-2d
git lfs pull
lake build
lake env lean Audit.lean
```

The `certificates/` directory contains 98 required matrix-certificate files,
about 1.04 GB in total, stored with Git LFS. These are inputs checked by the
Lean proofs of the finite quadratic cases. Download them before building.
Use a Git LFS clone as shown above to obtain the complete project; a GitHub
source ZIP may contain LFS pointers instead of the certificate data.

The toolchain is Lean **4.35.0-rc3**. Mathlib is pinned to commit
`8accc04827c389e678c3ef83e623b402e7480394`; the Lake configuration and manifest
pin the dependencies. The full local build passed all 10,914 jobs, and the
standard axiom audit passed. The main theorem depends only on `propext`,
`Classical.choice`, and `Quot.sound`.

See [`VERIFY.txt`](VERIFY.txt) for verification details. If certificate inputs
change, rebuild with a fresh `.lake/build` directory because their file reads
are not tracked by Lake's dependency graph.

## Source layout

- `Froberg/`: the formalization, including the main theorem and its statement.
- `Quartic/`: the quadratic endpoint foundation and certificate checkers.
- `OAI/`: the imported polynomial equidistribution lemmas.
- `certificates/finite/`: finite-case certificate data, managed by Git LFS.
- `Audit.lean`: the standard axiom audit.
- `DirectAudit.lean`: an optional, more expensive dependency traversal.

Imported-source provenance and certificate hashes are recorded in
[`OAI/PROVENANCE.txt`](OAI/PROVENANCE.txt),
[`Quartic/PROVENANCE.txt`](Quartic/PROVENANCE.txt), and
[`Quartic/DATA_PROVENANCE.txt`](Quartic/DATA_PROVENANCE.txt).
The imported OAI modules retain their [Apache 2.0 license](OAI/LICENSE).
