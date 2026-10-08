import Quartic.GenericF13Endpoint
import Quartic.ConvolutionAllRange

/-! # A varying-presentation F₁₃ witness and coefficient open for all m≥28 -/
noncomputable section
namespace Quartic.GenericF13AllRange
open Module MvPolynomial GeneralF13 GenericF13 GenericF13Endpoint
open ConvolutionPresentation ConvolutionOuterIncidence ConvolutionOuterGeneric
open ConvolutionCubicGeneric ProfileCertificate UniformEndpoint ConvolutionAllRange
variable {K : Type*} [Field K]

/-- An actual witness exists in the correct m-variable and c-column unrestricted family. -/
theorem exists_endpoint_witness [Infinite K] (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    ∃ E : GeneralF13.Mixed K m (mixedCount m upper),
      ∃ Q : Quadrics K m (upperEndpoint m), GenericF13.Conditions E Q := by
  obtain ⟨Q,hQ⟩ := exists_common_conditions (K := K) m hm upper
  have hc := endpoint_columns_range m hm upper
  have ht : 2 ≤ coreP (mixedCount m upper)+1 := by unfold coreP; omega
  have hv := ConvolutionAllRange.endpoint_variable_count m hm upper
  have hcols : coreP (mixedCount m upper)+1+2 = mixedCount m upper := by unfold coreP; omega
  have h : ∃ E : GeneralF13.Mixed K
      (coreP (mixedCount m upper)+1+freeW m (mixedCount m upper))
      (coreP (mixedCount m upper)+1+2),
      ∃ Q : Quadrics K (coreP (mixedCount m upper)+1+freeW m (mixedCount m upper))
        (upperEndpoint m), GenericF13.Conditions E Q :=
    ⟨convolutionMixed K _ _, Q, convolution_conditions ht Q hQ.2.1 hQ.2.2.2.1⟩
  exact transport_witness hv hcols h

/-- Nonempty principal-open F₁₃ injectivity in the full actual mixed/child coefficient family. -/
theorem generic_endpoint_conditions [Infinite K] (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    ∃ D : MvPolynomial (MiddleCoordinates.CoefficientIndex m (mixedCount m upper) (upperEndpoint m)) K,
      (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
        GenericF13.Conditions (MiddleCoordinates.decode a).1 (MiddleCoordinates.decode a).2 := by
  obtain ⟨E,Q,hQ,hC,hF⟩ := exists_endpoint_witness (K := K) m hm upper
  obtain ⟨D,hD,hgood⟩ := GenericF13.principal_open_of_witness E Q hQ hC hF
  exact ⟨D,⟨_,hD⟩,hgood⟩

end Quartic.GenericF13AllRange
