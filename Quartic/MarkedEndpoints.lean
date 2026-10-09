module

public import Quartic.MarkedLowerWitness
public import Quartic.UniformEndpoint

@[expose] public section

/-! The induction property retaining a square at positive lower endpoints. -/

namespace Quartic

/-- Generic maximal rank at every count, together with a marked lower witness
when the lower Euler surplus is positive. -/
def MarkedEndpoints (K : Type*) [Field K] (n : ℕ) : Prop :=
  (∀ r : ℕ, r ≤ (n + 1).choose 2 → GenericQuartic K n r) ∧
    (0 < Counts.chi n (UniformEndpoint.lowerEndpoint n) →
      MarkedLowerWitness K n (UniformEndpoint.lowerEndpoint n))

/-- Three initial dimensions and a three-variable transfer establish the
marked endpoint property in every subsequent dimension. -/
theorem markedEndpoints_of_three_step {K : Type*} [Field K] (start : ℕ)
    (h₀ : MarkedEndpoints K start) (h₁ : MarkedEndpoints K (start + 1))
    (h₂ : MarkedEndpoints K (start + 2))
    (hstep : ∀ n : ℕ, start ≤ n → MarkedEndpoints K n → MarkedEndpoints K (n + 3)) :
    ∀ n : ℕ, start ≤ n → MarkedEndpoints K n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      by_cases h : n = start
      · subst n
        exact h₀
      by_cases h' : n = start + 1
      · subst n
        exact h₁
      by_cases h'' : n = start + 2
      · subst n
        exact h₂
      have hge : start + 3 ≤ n := by omega
      have hpred : start ≤ n - 3 := by omega
      have hlt : n - 3 < n := by omega
      have hnext := hstep (n - 3) hpred (ih (n - 3) hlt hpred)
      simpa only [Nat.sub_add_cancel (by omega : 3 ≤ n)] using hnext

end Quartic
