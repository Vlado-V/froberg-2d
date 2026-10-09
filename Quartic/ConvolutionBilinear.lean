module

public import Quartic.ConvolutionEvaluation
public import Quartic.ConvolutionHilbert
public import Quartic.RationalCurve
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

@[expose] public section

/-!
# Symmetric bilinear coordinates for the actual quadratic inverse factor

The coefficients of the proved bivariate factor space are a symmetric
matrix. The resulting bilinear form is faithful, and its evaluation on the
rational normal curve is ordinary evaluation in the second polynomial slot.
-/

noncomputable section
namespace Quartic.ConvolutionBilinear
open MvPolynomial ConvolutionSymmetric ConvolutionConstantSlot
open ConvolutionFactor ConvolutionEvaluation
variable {K : Type*} [Field K] {p : ℕ}

/-- The ordinary coefficient matrix of a symmetric bivariate polynomial. -/
def coefficientMatrix : symmetricSpace K p →ₗ[K] Matrix (Fin p) (Fin p) K where
  toFun H i j := H.val.coeff (pairExponent i.val j.val)
  map_add' H G := by
    funext i j
    change (H.val + G.val).coeff _ = H.val.coeff _ + G.val.coeff _
    simp
  map_smul' a H := by
    funext i j
    change (a • H.val).coeff _ = a * H.val.coeff _
    simp

/-- All coefficients in the defining rectangle are retained by this matrix. -/
theorem coefficientMatrix_injective : Function.Injective
    (coefficientMatrix (K := K) (p := p)) := by
  intro H G h
  apply Subtype.ext
  rw [← fromCoefficients_reconstruct H.val H.property,
    ← fromCoefficients_reconstruct G.val G.property]
  congr 1
  funext ij
  exact congrArg (fun A : Matrix (Fin p) (Fin p) K => A ij.val.1 ij.val.2) h

/-- Turn the actual polynomial coefficients into a bilinear form. -/
def bilinearMap : symmetricSpace K p →ₗ[K]
    ((Fin p → K) →ₗ[K] (Fin p → K) →ₗ[K] K) :=
  Matrix.toBilin'.toLinearMap.comp coefficientMatrix

theorem bilinearMap_injective : Function.Injective (bilinearMap (K := K) (p := p)) :=
  Matrix.toBilin'.injective.comp coefficientMatrix_injective

/-- Polynomial slot symmetry is exactly symmetry of this bilinear form. -/
theorem bilinearMap_symmetric (H : symmetricSpace K p) (x y : Fin p → K) :
    bilinearMap H x y = bilinearMap H y x := by
  apply (Matrix.isSymm_toBilin'_iff_isSymm.mpr ?_).eq x y
  ext i j
  exact H.property.2 j i

@[simp] theorem bilinearMap_single (H : symmetricSpace K p) (i j : Fin p) :
    bilinearMap H (Pi.single i 1) (Pi.single j 1) =
      H.val.coeff (pairExponent i.val j.val) :=
  Matrix.toBilin'_single _ i j

/-- An explicit complete coefficient expansion, with no multiplicity factors. -/
theorem symmetric_expansion (H : symmetricSpace K p) :
    H.val = ∑ i : Fin p, ∑ j : Fin p,
      monomial (pairExponent i.val j.val) (H.val.coeff (pairExponent i.val j.val)) := by
  conv_lhs => rw [← fromCoefficients_reconstruct H.val H.property, fromCoefficients_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  by_cases hij : i ≤ j
  · rw [sortedPair_of_le i j hij]
  · rw [sortedPair_swap i j, sortedPair_of_le j i (le_of_not_ge hij)]
    exact (H.property.2 i j).symm

/-- Evaluate only the second ordinary variable, retaining the first. -/
def evaluateOrdinarySecond (a : K) : Quartic.Poly K 2 →ₐ[K] Quartic.Poly K 1 :=
  aeval fun i => if i = 0 then X 0 else C a

@[simp] theorem evaluateOrdinarySecond_monomial (a c : K) (i j : ℕ) :
    evaluateOrdinarySecond a (monomial (pairExponent i j) c) =
      monomial (Finsupp.single 0 i) (c * a ^ j) := by
  have hm : (monomial (pairExponent i j) c : Quartic.Poly K 2) =
      C c * (X 0) ^ i * (X 1) ^ j := by
    rw [X_pow_eq_monomial, X_pow_eq_monomial, C_mul_monomial, monomial_mul_monomial]
    simp [pairExponent]
  rw [hm, map_mul, map_mul, map_pow, map_pow]
  simp only [evaluateOrdinarySecond, aeval_C, aeval_X, ite_eq_left,
    one_ne_zero, ite_false, MvPolynomial.algebraMap_eq]
  rw [← C_pow, mul_assoc, mul_comm ((X 0 : Quartic.Poly K 1) ^ i),
    ← mul_assoc, ← map_mul, X_pow_eq_monomial, C_mul_monomial]
  simp


/-- Evaluated polynomial coefficients are the expected matrix-row evaluations. -/
theorem evaluateOrdinarySecond_coeff (a : K) (H : symmetricSpace K p) (i : Fin p) :
    (evaluateOrdinarySecond a H.val).coeff (Finsupp.single 0 i.val) =
      ∑ j : Fin p, H.val.coeff (pairExponent i.val j.val) * a ^ j.val := by
  classical
  conv_lhs => rw [symmetric_expansion H]
  simp only [map_sum, evaluateOrdinarySecond_monomial, coeff_sum, coeff_monomial]
  have heq (k : Fin p) :
      (Finsupp.single (0 : Fin 1) k.val : Fin 1 →₀ ℕ) = Finsupp.single 0 i.val ↔ k = i := by
    rw [(Finsupp.single_injective (0 : Fin 1)).eq_iff, Fin.val_inj]
  simp_rw [heq]
  simp

/-- Bilinear evaluation on the rational normal curve equals evaluation in one
ordinary polynomial slot. -/
theorem bilinearMap_curve_single (a : K) (H : symmetricSpace K p) (i : Fin p) :
    bilinearMap H (RationalCurve.point p a) (Pi.single i 1) =
      (evaluateOrdinarySecond a H.val).coeff (Finsupp.single 0 i.val) := by
  classical
  rw [bilinearMap_symmetric, evaluateOrdinarySecond_coeff]
  change Matrix.toBilin' (coefficientMatrix H) (Pi.single i 1) (RationalCurve.point p a) = _
  rw [Matrix.toBilin'_apply]
  simp [Pi.single_apply, coefficientMatrix, RationalCurve.point]
  rfl

/-- Restoring the absent distinguished variable commutes with evaluation. -/
theorem evaluateSecond_rename (a : K) (H : Quartic.Poly K 2) :
    evaluateSecond a (rename Option.some H) =
      rename Option.some (evaluateOrdinarySecond a H) := by
  have h : (evaluateSecond a).comp (rename Option.some) =
      (rename Option.some).comp (evaluateOrdinarySecond a) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [evaluateSecond, evaluateOrdinarySecond]
  exact congrArg (fun f : Quartic.Poly K 2 →ₐ[K] Slots K 1 => f H) h

end Quartic.ConvolutionBilinear
