module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

/-!
# Lifting certified binary minors to characteristic zero

These statements formalize the minor-lifting step in `finite_bases.tex`.
They do not assert that any of the attached large binary certificates has
already been verified in Lean: a nonzero binary determinant is an explicit
hypothesis of the lifting theorems.
-/

namespace Quartic.MinorLift

noncomputable section

section RingHom

variable {R S ι : Type*} [CommRing R] [CommRing S]
  [Fintype ι] [DecidableEq ι]

/-- A determinant that survives a coefficient specialization was nonzero
before specialization. This also applies to polynomial coefficient rings. -/
theorem det_ne_zero_of_specialization (f : R →+* S) (M : Matrix ι ι R)
    (hM : (M.map f).det ≠ 0) : M.det ≠ 0 := by
  intro hz
  apply hM
  change (f.mapMatrix M).det = 0
  rw [← f.map_det M, hz, map_zero]

/-- An injective coefficient homomorphism preserves nonzero determinants. -/
theorem det_ne_zero_under_injective_map (f : R →+* S)
    (hf : Function.Injective f) (M : Matrix ι ι R) (hM : M.det ≠ 0) :
    (M.map f).det ≠ 0 := by
  change (f.mapMatrix M).det ≠ 0
  rw [← f.map_det M, ← f.map_zero]
  exact hf.ne hM

end RingHom

section Binary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A nonzero determinant modulo two proves a nonzero integer determinant. -/
theorem integer_det_ne_zero_of_binary (M : Matrix ι ι ℤ)
    (hbinary : (M.map (Int.castRingHom (ZMod 2))).det ≠ 0) :
    M.det ≠ 0 :=
  det_ne_zero_of_specialization (Int.castRingHom (ZMod 2)) M hbinary

/-- The same integer minor is nonzero over every characteristic-zero field. -/
theorem charZero_det_ne_zero_of_binary {K : Type*} [Field K] [CharZero K]
    (M : Matrix ι ι ℤ)
    (hbinary : (M.map (Int.castRingHom (ZMod 2))).det ≠ 0) :
    (M.map (Int.castRingHom K)).det ≠ 0 := by
  apply det_ne_zero_under_injective_map (Int.castRingHom K) Int.cast_injective
  exact integer_det_ne_zero_of_binary M hbinary

/-- A certified binary minor of a rectangular integer matrix gives the same
rank lower bound after mapping all coefficients to a characteristic-zero field.
The index maps may be arbitrary: a nonzero minor already forces the necessary
row and column independence. -/
theorem charZero_rank_lower_bound_of_binary_minor
    {K m n : Type*} [Field K] [CharZero K] [Fintype m] [Fintype n]
    (M : Matrix m n ℤ) (rows : ι → m) (cols : ι → n)
    (hbinary : ((M.submatrix rows cols).map
      (Int.castRingHom (ZMod 2))).det ≠ 0) :
    Fintype.card ι ≤ (M.map (Int.castRingHom K)).rank := by
  have hdet : ((M.map (Int.castRingHom K)).submatrix rows cols).det ≠ 0 :=
    charZero_det_ne_zero_of_binary (M.submatrix rows cols) hbinary
  calc
    Fintype.card ι =
        ((M.map (Int.castRingHom K)).submatrix rows cols).rank :=
      (Matrix.rank_of_det_ne_zero hdet).symm
    _ ≤ (M.map (Int.castRingHom K)).rank := Matrix.rank_submatrix_le _ rows cols

end Binary

end

end Quartic.MinorLift
