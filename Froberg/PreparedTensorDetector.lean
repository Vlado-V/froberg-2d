import Froberg.CoreTensorProjection

/-! The exact tensor detector annihilates the actual prepared background.
Only the scalar ideal, quadratic output kernel, and explicit private term
are needed; all higher components disappear under X-degree extraction. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] {h m d : ℕ}

/-- The concrete low-component assumptions imply the precise background
annihilation required by the homogeneous C.2 separation construction. -/
theorem prepared_tensor_detector_annihilates {X : Type*} [AddCommGroup X] [Module K X]
    (hd : 2 ≤ d) (T : Poly K h →ₗ[K] X)
    (hT : T.comp (homogeneousComponent 2) = T)
    (Q0 Q : Submodule K (Poly K m)) (D : Submodule K (Poly K h))
    (hQ : Q0 * Forms K m (d-2) ≤ Q) (hD : D ≤ T.ker)
    (P : Submodule K (Poly K (h+m)))
    (hP : P * polynomialTensorSpace (Forms K h 1) (Forms K m (d-1)) ≤
      (splitPolynomialDetector T Q).ker)
    (W : Submodule K (Forms K (h+m) d))
    (H : PreparedLowComponents W (polynomialTensorSpace (Forms K h 0) Q0) P
      (polynomialTensorSpace D (Forms K m (d-2)))) :
    ∀ w : Forms K (h+m) d, w ∈ W → ∀ a : Forms K (h+m) d,
      splitPolynomialDetector T Q (w.val*a.val) = 0 := by
  apply prepared_background_annihilated W _ _ _ H (splitPolynomialDetector T Q)
  · exact splitPolynomialDetector_supported T Q hT
  · have hc2 : coreCoefficientSpace K h m d 2 =
        polynomialTensorSpace (Forms K h 2) (Forms K m (d-2)) := by
      have hh : 2+(d-2)=d := by omega
      simpa only [hh] using (coreCoefficientSpace_eq_polynomialTensorSpace (K := K) (h := h) (m := m) 2 (d-2))
    have hc1 : coreCoefficientSpace K h m d 1 =
        polynomialTensorSpace (Forms K h 1) (Forms K m (d-1)) := by
      have hh : 1+(d-1)=d := by omega
      simpa only [hh] using (coreCoefficientSpace_eq_polynomialTensorSpace (K := K) (h := h) (m := m) 1 (d-1))
    have hc0 : coreCoefficientSpace K h m d 0 =
        polynomialTensorSpace (Forms K h 0) (Forms K m d) := by
      simpa only [zero_add] using (coreCoefficientSpace_eq_polynomialTensorSpace (K := K) (h := h) (m := m) 0 d)
    unfold preparedProductDenominator
    rw [hc2,hc1,hc0]
    refine sup_le (sup_le ?_ hP) ?_
    · exact polynomialTensorSpace_product_le_ker_right T Q _ _ _ _ hQ
    · apply polynomialTensorSpace_product_le_ker_left T Q
      simpa only [Forms,homogeneousSubmodule_zero,mul_one] using hD

end Froberg
