import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Module

/-!
# The algebraic core of the two-order deformation

This file formalizes the first and second response identities used in
`transfer.tex`, and a polynomial matrix criterion that turns a nonzero
normalized leading minor into a rank lower bound at some specialization.
The construction of the manuscript's homology spaces, the incidence argument,
and the verification that its corrections satisfy this criterion are separate
obligations; they are not assumed as new axioms here.
-/

namespace Quartic

noncomputable section

section Responses

variable {R V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- A cycle of the split map has precisely the expected first response. -/
theorem deformation_first_response (M₀ M₁ : V →ₗ[R] W)
    (ε : R) (a : V) (ha : M₀ a = 0) :
    (M₀ + ε • M₁) a = ε • M₁ a := by
  simp [ha]

/-- Cancelling the first response leaves the second response, exactly. -/
theorem deformation_second_response (M₀ M₁ : V →ₗ[R] W)
    (ε : R) (a a₁ : V) (ha : M₀ a = 0)
    (hc : M₀ a₁ = -M₁ a) :
    (M₀ + ε • M₁) (a + ε • a₁) = ε ^ 2 • M₁ a₁ := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    ha, hc, zero_add, smul_add, smul_neg, smul_smul, pow_two]
  abel

end Responses

section PolynomialMatrices

open Polynomial

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- Multiply column `j` by the deformation parameter to its assigned order.
Orders zero, one and two describe split pivots and the two response groups. -/
def weightedColumns (B : Matrix ι ι K[X]) (order : ι → ℕ) : Matrix ι ι K[X] :=
  fun i j => X ^ order j * B i j

theorem weightedColumns_det (B : Matrix ι ι K[X]) (order : ι → ℕ) :
    (weightedColumns B order).det =
      (∏ j, (X : K[X]) ^ order j) * B.det := by
  exact Matrix.det_mul_row (fun j => (X : K[X]) ^ order j) B

/-- A nonzero determinant at parameter zero makes the determinant polynomial
nonzero. This concerns the normalized matrix, before restoring column orders. -/
theorem determinant_ne_zero_of_leading_minor (B : Matrix ι ι K[X])
    (hB : (B.map (evalRingHom (0 : K))).det ≠ 0) : B.det ≠ 0 := by
  intro hz
  apply hB
  change ((evalRingHom (0 : K)).mapMatrix B).det = 0
  rw [← (evalRingHom (0 : K)).map_det B, hz, map_zero]

/-- Restoring any finite column orders preserves nonvanishing over `K[X]`. -/
theorem weightedColumns_det_ne_zero (B : Matrix ι ι K[X]) (order : ι → ℕ)
    (hB : (B.map (evalRingHom (0 : K))).det ≠ 0) :
    (weightedColumns B order).det ≠ 0 := by
  rw [weightedColumns_det]
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ X_ne_zero)
  · exact determinant_ne_zero_of_leading_minor B hB

/-- Over an infinite field, a square polynomial matrix with nonzero determinant
has an invertible specialization. -/
theorem exists_specialization_full_rank [Infinite K] (D : Matrix ι ι K[X])
    (hD : D.det ≠ 0) :
    ∃ ε : K, (D.map (evalRingHom ε)).rank = Fintype.card ι := by
  classical
  have hex : ∃ ε : K, D.det.eval ε ≠ 0 := by
    by_contra h
    push Not at h
    exact hD (Polynomial.zero_of_eval_zero D.det h)
  obtain ⟨ε, hε⟩ := hex
  refine ⟨ε, Matrix.rank_of_det_ne_zero ?_⟩
  change ((evalRingHom ε).mapMatrix D).det ≠ 0
  rwa [← (evalRingHom ε).map_det D]

/-- The selected normalized leading minor yields an actual rank bound.

`L` and `V` encode polynomial row operations and corrected source vectors.
Thus the hypothesis permits split pivot columns and columns whose first
nonzero response occurs at different orders. It requires the factorization
explicitly; in particular, it does not silently assume the manuscript's
geometric construction of that factorization.
-/
theorem rank_specialization_of_weighted_factorization
    {m n : Type*} [Fintype m] [Fintype n] [Infinite K]
    (M : Matrix m n K[X]) (L : Matrix ι m K[X])
    (V : Matrix n ι K[X]) (B : Matrix ι ι K[X]) (order : ι → ℕ)
    (hfactor : L * M * V = weightedColumns B order)
    (hleading : (B.map (evalRingHom (0 : K))).det ≠ 0) :
    ∃ ε : K, Fintype.card ι ≤ (M.map (evalRingHom ε)).rank := by
  classical
  have hD : (L * M * V).det ≠ 0 := by
    rw [hfactor]
    exact weightedColumns_det_ne_zero B order hleading
  obtain ⟨ε, hε⟩ := exists_specialization_full_rank (L * M * V) hD
  refine ⟨ε, ?_⟩
  rw [Matrix.map_mul, Matrix.map_mul] at hε
  calc
    Fintype.card ι =
        (L.map (evalRingHom ε) * M.map (evalRingHom ε) *
          V.map (evalRingHom ε)).rank := hε.symm
    _ ≤ (L.map (evalRingHom ε) * M.map (evalRingHom ε)).rank :=
      Matrix.rank_mul_le_left _ _
    _ ≤ (M.map (evalRingHom ε)).rank := Matrix.rank_mul_le_right _ _

/-- In fact the same rank bound holds outside a finite set of parameter values.
Over an infinite field this supplies the usual generic rank conclusion. -/
theorem generic_rank_of_weighted_factorization
    {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n K[X]) (L : Matrix ι m K[X])
    (V : Matrix n ι K[X]) (B : Matrix ι ι K[X]) (order : ι → ℕ)
    (hfactor : L * M * V = weightedColumns B order)
    (hleading : (B.map (evalRingHom (0 : K))).det ≠ 0) :
    ∀ᶠ ε : K in Filter.cofinite,
      Fintype.card ι ≤ (M.map (evalRingHom ε)).rank := by
  classical
  have hD : (L * M * V).det ≠ 0 := by
    rw [hfactor]
    exact weightedColumns_det_ne_zero B order hleading
  refine (Polynomial.eventually_eval_ne_zero_cofinite hD).mono ?_
  intro ε hε
  have hminor : ((L * M * V).map (evalRingHom ε)).det ≠ 0 := by
    change ((evalRingHom ε).mapMatrix (L * M * V)).det ≠ 0
    rwa [← (evalRingHom ε).map_det (L * M * V)]
  have hrank := Matrix.rank_of_det_ne_zero hminor
  rw [Matrix.map_mul, Matrix.map_mul] at hrank
  calc
    Fintype.card ι =
        (L.map (evalRingHom ε) * M.map (evalRingHom ε) *
          V.map (evalRingHom ε)).rank := hrank.symm
    _ ≤ (L.map (evalRingHom ε) * M.map (evalRingHom ε)).rank :=
      Matrix.rank_mul_le_left _ _
    _ ≤ (M.map (evalRingHom ε)).rank := Matrix.rank_mul_le_right _ _

end PolynomialMatrices

end

end Quartic
