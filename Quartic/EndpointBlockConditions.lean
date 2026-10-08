import Quartic.SimultaneousBlockConditions
import Quartic.UniformScalar

/-!
# Simultaneous actual block conditions at every transfer endpoint

The checked finite and uniform arithmetic budgets are applied to the actual
middle, augmented, and trace families, for every child dimension m at least 28.
This proves these component conditions on one shared nonempty principal open;
it does not assume or prove the full split-complex or deformation assembly.
-/
noncomputable section
namespace Quartic.EndpointBlockConditions
open Counts UniformEndpoint SimultaneousBlockConditions

/-- The same structural budgets hold at both canonical endpoints in every
child dimension used by the manuscript's transfer. -/
theorem structural_counts (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    let q := upperEndpoint m
    let c := mixedCount m upper
    let w₀ := m - 2 * c
    4 ≤ c ∧ c ≤ m ∧ (m : ℤ) * q ≤ b3 m ∧
      3 ≤ alpha m q - b2 c ∧ (c : ℤ) * w₀ + b2 w₀ ≤ q := by
  by_cases hsmall : m ≤ 319
  · have h := FiniteCounts.structural_binomial_counts m hm hsmall upper
    rw [upperEndpoint_eq_table m (by omega), mixedCount_eq_table m hsmall upper]
    exact h
  · exact UniformScalar.structural_binomial_counts m (by omega) upper

/-- Natural-number budgets match those required by the actual block maps. -/
theorem block_budgets (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    let q := upperEndpoint m
    let c := mixedCount m upper
    c ≤ m ∧ q + (c + 1).choose 2 + 3 ≤ (m + 1).choose 2 ∧
      (((m + 1) / 2 ≤ c ∧ c ≤ 3*m) ∨
        (2*c ≤ m ∧ c*(m-2*c) + (m-2*c+1).choose 2 ≤ q)) := by
  obtain ⟨_, hc, _, haug, hrepair⟩ := structural_counts m hm upper
  dsimp only at hc haug hrepair ⊢
  refine ⟨hc, ?_, ?_⟩
  · simp only [alpha, b2] at haug
    omega
  · by_cases hcovered : (m + 1) / 2 ≤ mixedCount m upper
    · exact Or.inl ⟨hcovered, by omega⟩
    · apply Or.inr
      refine ⟨by omega, ?_⟩
      unfold b2 at hrepair
      exact_mod_cast hrepair

/-- For every m≥28 and both parent endpoints, the same actual coefficient
family satisfies middle surjectivity, augmented injectivity, and trace bounds
on one nonempty principal open. -/
theorem generic_block_conditions {K : Type*} [Field K] [Infinite K]
    (m : ℕ) (hm : 28 ≤ m) (upper : Bool) (h2 : (2 : K) ≠ 0) :
    GenericBlockConditions K m (mixedCount m upper) (upperEndpoint m) := by
  obtain ⟨hc, haug, hmid⟩ := block_budgets m hm upper
  exact genericBlockConditions_of_budgets hc haug hmid h2

/-- An actual common choice of mixed coefficients, child quadrics, and pure motions. -/
theorem exists_block_conditions {K : Type*} [Field K] [Infinite K]
    (m : ℕ) (hm : 28 ≤ m) (upper : Bool) (h2 : (2 : K) ≠ 0) :
    ∃ a : AugmentedGeneric.ParameterIndex m (mixedCount m upper) (upperEndpoint m) → K,
      BlockConditions a := by
  obtain ⟨D, ⟨a, ha⟩, h⟩ := generic_block_conditions m hm upper h2
  exact ⟨a, h a ha⟩

end Quartic.EndpointBlockConditions
