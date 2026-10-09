module

public import Quartic.SimultaneousBlockConditionsOmega
public import Quartic.EndpointBlockConditions

@[expose] public section

/-!
# Simultaneous actual block conditions at every transfer endpoint

The checked finite and uniform arithmetic budgets are applied to the actual
middle, augmented, and trace families, for every child dimension m at least 28.
This proves these component conditions on one shared nonempty principal open;
it does not assume or prove the full split-complex or deformation assembly.
-/
noncomputable section
namespace Quartic.EndpointBlockConditionsOmega
open Counts UniformEndpoint SimultaneousBlockConditionsOmega

open EndpointBlockConditions

/-- For every m≥28 and both parent endpoints, the same actual coefficient
family satisfies middle surjectivity, augmented injectivity, and trace bounds
on one nonempty principal open. -/
theorem generic_block_conditions {K : Type*} [Field K] [Infinite K]
    (ω : K) (m : ℕ) (hm : 28 ≤ m) (upper : Bool) (hω : ω ≠ 0) (hω1 : ω ≠ -1) :
    GenericBlockConditions K ω m (mixedCount m upper) (upperEndpoint m) := by
  obtain ⟨hc, haug, hmid⟩ := block_budgets m hm upper
  exact genericBlockConditions_of_budgets ω hc haug hmid hω hω1

/-- An actual common choice of mixed coefficients, child quadrics, and pure motions. -/
theorem exists_block_conditions {K : Type*} [Field K] [Infinite K]
    (ω : K) (m : ℕ) (hm : 28 ≤ m) (upper : Bool) (hω : ω ≠ 0) (hω1 : ω ≠ -1) :
    ∃ a : AugmentedGeneric.ParameterIndex m (mixedCount m upper) (upperEndpoint m) → K,
      BlockConditions ω a := by
  obtain ⟨D, ⟨a, ha⟩, h⟩ := generic_block_conditions ω m hm upper hω hω1
  exact ⟨a, h a ha⟩

end Quartic.EndpointBlockConditionsOmega
