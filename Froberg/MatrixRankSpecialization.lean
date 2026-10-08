import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

/-!
# Matrix ranks over polynomial fraction fields and at specializations

The rank witnesses used here are square compressions `Y * M * X`.
This permits clearing their denominators without choosing particular minors.
-/

namespace Froberg

open Matrix Module

variable {K m n : Type*} [Field K]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- A matrix of rank `r` admits a square compression equal to the identity
of size `r`.  The witnesses are obtained from a basis of its actual image. -/
theorem exists_rank_compression (M : Matrix m n K) :
    ∃ X : Matrix n (Fin M.rank) K, ∃ Y : Matrix (Fin M.rank) m K,
      Y * M * X = 1 := by
  classical
  let f := M.mulVecLin
  change ∃ X : Matrix n (Fin (finrank K f.range)) K,
    ∃ Y : Matrix (Fin (finrank K f.range)) m K, Y * M * X = 1
  let b := Module.finBasis K f.range
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨p, hp⟩ := f.range.subtype.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr f.range.injective_subtype)
  let x := s.comp b.equivFun.symm.toLinearMap
  let y := b.equivFun.toLinearMap.comp p
  refine ⟨LinearMap.toMatrix' x, LinearMap.toMatrix' y, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix' x,
    Matrix.toLin'_toMatrix' y, Matrix.toLin'_one]
  apply LinearMap.ext
  intro v
  change b.equivFun (p (f (s (b.equivFun.symm v)))) = v
  have hfs : f (s (b.equivFun.symm v)) = (b.equivFun.symm v).val :=
    congrArg Subtype.val (LinearMap.congr_fun hs (b.equivFun.symm v))
  have hpv : p (b.equivFun.symm v).val = b.equivFun.symm v :=
    LinearMap.congr_fun hp (b.equivFun.symm v)
  rw [hfs, hpv]
  exact b.equivFun.apply_symm_apply v

/-- Any nonsingular square compression gives a lower bound for rank. -/
theorem rank_ge_of_compression_det_ne_zero
    {r : ℕ} (M : Matrix m n K) (X : Matrix n (Fin r) K) (Y : Matrix (Fin r) m K)
    (hdet : (Y * M * X).det ≠ 0) : r ≤ M.rank := by
  have hle := (Matrix.rank_mul_le_left (Y * M) X).trans (Matrix.rank_mul_le_right Y M)
  rwa [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at hle

section Denominators

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F]

/-- A single nonzero scalar clears all entries of a finite matrix. -/
theorem exists_matrix_integer_multiple (A : Matrix m n F) :
    ∃ s : R, s ≠ 0 ∧ ∃ A₀ : Matrix m n R,
      A₀.map (algebraMap R F) = algebraMap R F s • A := by
  classical
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors R) (fun ij : m × n => A ij.1 ij.2)
  choose U hU using hs
  refine ⟨s, nonZeroDivisors.ne_zero s.property, (fun i j => U (i, j)), ?_⟩
  ext i j
  change algebraMap R F (U (i, j)) = algebraMap R F (s : R) * A i j
  simpa only [Algebra.smul_def] using hU (i, j)

end Denominators

section Polynomial

variable {σ F : Type*} [Field F]
  [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]

/-- Every pointwise specialization has rank at most the rank over the
fraction field of the polynomial coefficient ring. -/
theorem specialization_rank_le_fraction_rank
    (M : Matrix m n (MvPolynomial σ K)) (a : σ → K) :
    (M.map (MvPolynomial.eval a)).rank ≤
      (M.map (algebraMap (MvPolynomial σ K) F)).rank := by
  classical
  obtain ⟨X, Y, hYX⟩ := exists_rank_compression (M.map (MvPolynomial.eval a))
  let X₀ := X.map (MvPolynomial.C : K →+* MvPolynomial σ K)
  let Y₀ := Y.map (MvPolynomial.C : K →+* MvPolynomial σ K)
  let D := (Y₀ * M * X₀).det
  have heval : MvPolynomial.eval a D = 1 := by
    rw [show D = (Y₀ * M * X₀).det from rfl, RingHom.map_det]
    simpa [X₀, Y₀, Matrix.map_mul, Matrix.map_map, Function.comp_def] using
      congrArg Matrix.det hYX
  have hD : D ≠ 0 := by
    intro h
    rw [h, map_zero] at heval
    exact zero_ne_one heval
  have hDF : algebraMap (MvPolynomial σ K) F D ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial σ K) F)).mpr hD
  have hdet : ((Y₀.map (algebraMap (MvPolynomial σ K) F)) *
      M.map (algebraMap (MvPolynomial σ K) F) *
      X₀.map (algebraMap (MvPolynomial σ K) F)).det ≠ 0 := by
    simpa only [D, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul] using hDF
  exact rank_ge_of_compression_det_ne_zero _ _ _ hdet

/-- The fraction-field rank is attained at an actual ground-field point
when the ground field is infinite.  Denominators of the two compression
matrices are cleared before specializing. -/
theorem exists_specialization_rank_eq_fraction_rank [Infinite K]
    (M : Matrix m n (MvPolynomial σ K)) :
    ∃ a : σ → K, (M.map (MvPolynomial.eval a)).rank =
      (M.map (algebraMap (MvPolynomial σ K) F)).rank := by
  classical
  let φ := algebraMap (MvPolynomial σ K) F
  obtain ⟨X, Y, hYX⟩ := exists_rank_compression (M.map φ)
  obtain ⟨s, hs, X₀, hX⟩ := exists_matrix_integer_multiple (R := MvPolynomial σ K) X
  obtain ⟨t, ht, Y₀, hY⟩ := exists_matrix_integer_multiple (R := MvPolynomial σ K) Y
  change X₀.map φ = φ s • X at hX
  change Y₀.map φ = φ t • Y at hY
  have hsF : φ s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial σ K) F)).mpr hs
  have htF : φ t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial σ K) F)).mpr ht
  let D := (Y₀ * M * X₀).det
  have hcomp : (Y₀ * M * X₀).map φ =
      (φ t * φ s) • (1 : Matrix (Fin (M.map φ).rank) (Fin (M.map φ).rank) F) := by
    rw [Matrix.map_mul, Matrix.map_mul, hX, hY, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hYX]
  have hDF : φ D ≠ 0 := by
    rw [show D = (Y₀ * M * X₀).det from rfl, RingHom.map_det,
      RingHom.mapMatrix_apply, hcomp,
      Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (mul_ne_zero htF hsF)
  have hD : D ≠ 0 := by
    intro h
    exact hDF (by rw [h, map_zero])
  have hex : ∃ a : σ → K, MvPolynomial.eval a D ≠ 0 := by
    by_contra! h
    apply hD
    apply MvPolynomial.funext
    intro a
    simpa only [map_zero] using h a
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, Nat.le_antisymm (specialization_rank_le_fraction_rank (F := F) M a) ?_⟩
  apply rank_ge_of_compression_det_ne_zero (M.map (MvPolynomial.eval a))
    (X₀.map (MvPolynomial.eval a)) (Y₀.map (MvPolynomial.eval a))
  simpa only [D, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul] using ha

end Polynomial

end Froberg
