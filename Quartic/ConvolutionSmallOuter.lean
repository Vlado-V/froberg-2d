import Quartic.ConvolutionProfileChartBound
import Quartic.IteratedChartGeneric
import Quartic.ConvolutionOuterGeneric

/-!
# Generic actual outer injectivity for every endpoint with m≥28

For 28≤m≤40 the actual polynomial profile charts replace the full Grassmann
parameter count. Their ranks are the same actual initial ranks used by the
integral image certificate. Together with the previously proved m≥41 result,
this gives the complete canonical endpoint range.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Quartic.ConvolutionSmallOuter
open Module MvPolynomial ConvolutionFreePieces ConvolutionOuterIncidence
open ConvolutionOuterGeneric ProfileCertificate UniformEndpoint PolynomialBilinearCoordinates
variable {K : Type*} [Field K]

/-- The previously missing 26 endpoint configurations give genuine nonempty
principal opens of injective actual quotient multiplication maps. -/
theorem generic_outer_injective_small [Infinite K] (m : ℕ) (hmlo : 28 ≤ m)
    (hmhi : m ≤ 40) (upper : Bool) :
    ∃ P : MvPolynomial (Fin (finrank K (EndpointCoefficients K m upper))) K,
      (∃ Q : EndpointCoefficients K m upper,
        eval (coordinates K (EndpointCoefficients K m upper) Q) P ≠ 0) ∧
      ∀ Q : EndpointCoefficients K m upper,
        eval (coordinates K (EndpointCoefficients K m upper) Q) P ≠ 0 →
          Function.Injective (outerMap Q) := by
  have hc := ConvolutionFiniteImages.canonical_mixedCount_ge_four m hmlo (by omega) upper
  have ht : 2 ≤ coreP (mixedCount m upper)+1 := by unfold coreP; omega
  apply IteratedChartGeneric.generic_injective_of_equiv
    (ConvolutionProfileCoordinates.coordinates (K := K) (w := freeW m (mixedCount m upper)) ht)
    bilinear.flip
  intro L hL
  have h := ConvolutionProfileChartBound.profile_parameter_image_bound m hmlo hmhi upper ht
    (tupleSpan L) (tupleSpan_finrank_pos L hL)
  rw [←coefficientMap_finrank] at h
  exact h

/-- Actual outer injectivity now holds on a nonempty principal open for both
canonical endpoints in the entire child range m≥28. -/
theorem generic_outer_injective [Infinite K] (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    ∃ P : MvPolynomial (Fin (finrank K (EndpointCoefficients K m upper))) K,
      (∃ Q : EndpointCoefficients K m upper,
        eval (coordinates K (EndpointCoefficients K m upper) Q) P ≠ 0) ∧
      ∀ Q : EndpointCoefficients K m upper,
        eval (coordinates K (EndpointCoefficients K m upper) Q) P ≠ 0 →
          Function.Injective (outerMap Q) := by
  by_cases hsmall : m ≤ 40
  · exact generic_outer_injective_small m hm hsmall upper
  · exact ConvolutionOuterGeneric.generic_outer_injective m (by omega) upper

theorem exists_outer_injective [Infinite K] (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    ∃ Q : EndpointCoefficients K m upper,Function.Injective (outerMap Q) := by
  obtain ⟨_,⟨Q,hQ⟩,hgood⟩ := generic_outer_injective (K := K) m hm upper
  exact ⟨Q,hgood Q hQ⟩

end Quartic.ConvolutionSmallOuter
