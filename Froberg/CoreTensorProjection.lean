import Froberg.TensorProductDenominator
import Quartic.ConvolutionFreeMultiplication

/-! Compatibility of the exact X-degree projection with the split polynomial
tensor algebra and with the output detector used in C.2. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open MvPolynomial TensorProduct
open Quartic.FreeCoefficients Quartic.ConvolutionFreeMultiplication
variable {K : Type} [Field K] {h m i : ℕ}

/-- A free monomial coefficient does not affect the extracted X degree. -/
theorem coreComponent_liftCoeff (b : Fin m →₀ ℕ) (p : Poly K h) :
    coreComponent h m i (liftCoeff b p) = liftCoeff b (homogeneousComponent i p) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_freeCoeff
  intro e
  rw [map_sub,freeCoeff_coreComponent,freeCoeff_liftCoeff,freeCoeff_liftCoeff]
  split_ifs <;> simp

@[simp] theorem splitPolynomialEquiv_tmul_monomial (p : Poly K h) (b : Fin m →₀ ℕ) (c : K) :
    splitPolynomialEquiv (K := K) h m (p ⊗ₜ[K] monomial b c) = c • liftCoeff b p := by
  have he : (monomial b c : Poly K m) = c • monomial b 1 := by simp [smul_monomial,smul_eq_mul]
  rw [he,tmul_smul,map_smul,splitPolynomialEquiv_tmul,rename_monomial,
    Quartic.SplitTensor.child_rename_exponent,← liftCoeff_eq_mul]

/-- X-degree extraction acts only on the first tensor factor. -/
theorem coreComponent_split_tmul (p : Poly K h) (q : Poly K m) :
    coreComponent h m i (splitPolynomialEquiv (K := K) h m (p ⊗ₜ[K] q)) =
      splitPolynomialEquiv (K := K) h m (homogeneousComponent i p ⊗ₜ[K] q) := by
  induction q using MvPolynomial.induction_on' with
  | monomial b c =>
    rw [splitPolynomialEquiv_tmul_monomial,map_smul,coreComponent_liftCoeff,
      splitPolynomialEquiv_tmul_monomial]
  | add q r hq hr => simp only [tmul_add,map_add,hq,hr]

/-- An output detector supported in degree i is supported in the same exact
X degree after tensoring with the scalar quotient. -/
theorem splitPolynomialDetector_supported {X : Type*} [AddCommGroup X] [Module K X]
    (T : Poly K h →ₗ[K] X) (Q : Submodule K (Poly K m))
    (hT : T.comp (homogeneousComponent i) = T) :
    (splitPolynomialDetector T Q).comp (coreComponent h m i) = splitPolynomialDetector T Q := by
  apply LinearMap.ext
  intro p
  obtain ⟨v,rfl⟩ := (splitPolynomialEquiv (K := K) h m).surjective p
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    change splitPolynomialDetector T Q (coreComponent h m i (splitPolynomialEquiv (K := K) h m (a ⊗ₜ[K] b))) = _
    rw [coreComponent_split_tmul]
    simp only [splitPolynomialDetector,LinearMap.comp_apply,AlgEquiv.toLinearMap_apply,
      AlgEquiv.symm_apply_apply,TensorProduct.map_tmul]
    have he := LinearMap.congr_fun hT a
    change T (homogeneousComponent i a) = T a at he
    rw [he]
  | add u v hu hv => simp only [map_add,LinearMap.comp_apply] at hu hv ⊢; rw [hu,hv]

end Froberg
