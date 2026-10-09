module

public import Quartic.GenericF13AllRange
public import Quartic.EndpointCubicConditionsOmega

@[expose] public section

/-!
# One actual endpoint coefficient open including varying-presentation F₁₃

All mixed generators, child quadrics, and pure motions are the same in the
middle, augmented, trace, ordinary cubic, and F₁₃ conclusions.
-/
noncomputable section
namespace Quartic.EndpointF13AllRangeOmega
open Module MvPolynomial AugmentedGeneric SimultaneousMiddleOmega SimultaneousBlockConditionsOmega
open UniformEndpoint
variable {K : Type*} [Field K]

/-- A shared nonempty principal open of all actual component conditions proved so far. -/
theorem generic_endpoint_conditions [Infinite K] (ω : K) (m : ℕ) (hm : 28 ≤ m)
    (upper : Bool) (hω : ω ≠ 0) (hω1 : ω ≠ -1) :
    ∃ D : MvPolynomial (ParameterIndex m (mixedCount m upper) (upperEndpoint m)) K,
      (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
        BlockConditions ω a ∧ GenericF13.Conditions (coefficientMixed a) (coefficientChild a) ∧
          finrank K (CubicGeneric.CubicQuotient (coefficientChild a)) =
            (m+2).choose 3-m*upperEndpoint m := by
  classical
  obtain ⟨B,⟨b,hb⟩,hB⟩ := EndpointCubicConditionsOmega.generic_endpoint_blocks_and_cubic
    (K := K) ω m (by omega) upper hω hω1
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
theorem exists_endpoint_conditions [Infinite K] (ω : K) (m : ℕ) (hm : 28 ≤ m)
    (upper : Bool) (hω : ω ≠ 0) (hω1 : ω ≠ -1) :
    ∃ a : ParameterIndex m (mixedCount m upper) (upperEndpoint m) → K,
      BlockConditions ω a ∧ GenericF13.Conditions (coefficientMixed a) (coefficientChild a) ∧
        finrank K (CubicGeneric.CubicQuotient (coefficientChild a)) =
          (m+2).choose 3-m*upperEndpoint m := by
  obtain ⟨D,⟨a,ha⟩,hgood⟩ := generic_endpoint_conditions (K := K) ω m hm upper hω hω1
  exact ⟨a,hgood a ha⟩

end Quartic.EndpointF13AllRangeOmega
