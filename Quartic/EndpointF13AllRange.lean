import Quartic.GenericF13AllRange
import Quartic.EndpointCubicConditions

/-!
# One actual endpoint coefficient open including varying-presentation F₁₃

All mixed generators, child quadrics, and pure motions are the same in the
middle, augmented, trace, ordinary cubic, and F₁₃ conclusions.
-/
noncomputable section
namespace Quartic.EndpointF13AllRange
open Module MvPolynomial AugmentedGeneric SimultaneousMiddle SimultaneousBlockConditions
open UniformEndpoint
variable {K : Type*} [Field K]

/-- A shared nonempty principal open of all actual component conditions proved so far. -/
theorem generic_endpoint_conditions [Infinite K] (m : ℕ) (hm : 28 ≤ m)
    (upper : Bool) (h2 : (2 : K) ≠ 0) :
    ∃ D : MvPolynomial (ParameterIndex m (mixedCount m upper) (upperEndpoint m)) K,
      (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
        BlockConditions a ∧ GenericF13.Conditions (coefficientMixed a) (coefficientChild a) ∧
          finrank K (CubicGeneric.CubicQuotient (coefficientChild a)) =
            (m+2).choose 3-m*upperEndpoint m := by
  classical
  obtain ⟨B,⟨b,hb⟩,hB⟩ := EndpointCubicConditions.generic_endpoint_blocks_and_cubic
    (K := K) m (by omega) upper h2
  obtain ⟨F,⟨f,hf⟩,hF⟩ := GenericF13AllRange.generic_endpoint_conditions (K := K) m hm upper
  have hB0 : B ≠ 0 := by intro h; simp [h] at hb
  have hF0 : middlePullback F ≠ 0 := by
    intro h
    have he : eval (zeroMotionExtension f) (middlePullback F) ≠ 0 := by
      simpa only [eval_middlePullback, baseCoefficients_extension] using hf
    simp [h] at he
  obtain ⟨a₀,ha₀⟩ := nonempty_principal_intersection
    (![B,middlePullback F] : Fin 2 →
      MvPolynomial (ParameterIndex m (mixedCount m upper) (upperEndpoint m)) K)
    (by intro i; fin_cases i <;> assumption)
  refine ⟨B*middlePullback F,⟨a₀,?_⟩,?_⟩
  · rw [map_mul]
    exact mul_ne_zero (ha₀ 0) (ha₀ 1)
  · intro a ha
    rw [map_mul, mul_ne_zero_iff] at ha
    have hb := hB a ha.1
    have hf := hF (baseCoefficients a) (by simpa only [eval_middlePullback] using ha.2)
    exact ⟨hb.1,hf,hb.2.2⟩

/-- Existence of one actual coefficient point satisfying all these component conditions. -/
theorem exists_endpoint_conditions [Infinite K] (m : ℕ) (hm : 28 ≤ m)
    (upper : Bool) (h2 : (2 : K) ≠ 0) :
    ∃ a : ParameterIndex m (mixedCount m upper) (upperEndpoint m) → K,
      BlockConditions a ∧ GenericF13.Conditions (coefficientMixed a) (coefficientChild a) ∧
        finrank K (CubicGeneric.CubicQuotient (coefficientChild a)) =
          (m+2).choose 3-m*upperEndpoint m := by
  obtain ⟨D,⟨a,ha⟩,hgood⟩ := generic_endpoint_conditions (K := K) m hm upper h2
  exact ⟨a,hgood a ha⟩

end Quartic.EndpointF13AllRange
