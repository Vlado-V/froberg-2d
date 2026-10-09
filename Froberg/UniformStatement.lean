module

public import Froberg.Statement
public import Froberg.GenericMonotonicity
public import Froberg.PrefixTheorem
public import Froberg.LinearBase
public import Froberg.Truncation

@[expose] public section

/-! Field-uniform formulations for the revised manuscript.

The variable threshold is chosen before the coefficient field. In particular,
these propositions are stronger than a separate eventual statement for each
field. All generic conditions still refer to the actual polynomial quotient.
-/
noncomputable section
namespace Froberg

/-- The endpoint prediction with one threshold for every infinite field. -/
def UniformEndpointStatement (d : ℕ) : Prop :=
  ∃ N : ℕ, 1 ≤ N ∧ ∀ (K : Type) [Field K] [Infinite K],
    ∀ n : ℕ, N ≤ n → ∀ r : ℕ, r ≤ (n + d - 1).choose d →
      GenericEndpoint K n d r

/-- A common recurrence step and starting point for all infinite fields. -/
def UniformCriticalRecurrence (d : ℕ) : Prop :=
  ∃ h start : ℕ, 0 < h ∧ ∀ (K : Type) [Field K] [Infinite K],
    ∀ n : ℕ, start ≤ n → criticalDefect K (n + h) d ≤ criticalDefect K n d

/-- Theorem 1.1 of the revised paper: the threshold depends only on the degree. -/
def UniformMainStatement : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ N : ℕ, 1 ≤ N ∧
    ∀ (K : Type) [Field K] [Infinite K], ∀ n : ℕ, N ≤ n →
      ∀ r : ℕ, GenericHilbertThrough K n d r (2 * d)

theorem UniformMainStatement.specialize (h : UniformMainStatement)
    (K : Type) [Field K] [Infinite K] : MainStatement K := by
  intro d hd
  obtain ⟨N, hN, hfield⟩ := h d hd
  exact ⟨N, hN, hfield K⟩

/-- The prefix and linear base already have field-independent bounds, so only
the uniform endpoint theorem is needed for the full Hilbert-function result. -/
theorem uniformMainStatement_of_uniformEndpoints
    (hend : ∀ d : ℕ, 2 ≤ d → UniformEndpointStatement d) :
    UniformMainStatement := by
  intro d hd
  by_cases hd1 : d = 1
  · subst d
    refine ⟨1, le_rfl, ?_⟩
    intro K _ _ n hn r
    exact genericHilbertThrough_linear hn r
  have hd2 : 2 ≤ d := by omega
  obtain ⟨N, hNpos, hN⟩ := hend d hd2
  obtain ⟨T, hT⟩ := exists_endpoint_truncation_threshold hd2
  refine ⟨max N (max T (prefixThreshold d)), by omega, ?_⟩
  intro K _ _ n hn r
  have hnpos : 0 < n := by omega
  by_cases hr : (n + d - 1).choose d ≤ r
  · exact genericHilbertThrough_of_many_generators hnpos (by omega) hr _
  have hprefix := genericHilbertThrough_prefix (K := K) (by omega : 0 < d)
    (show prefixThreshold d ≤ n by omega) r
  apply (genericHilbertThrough_iff _).mpr
  intro j hj
  by_cases heq : j = 2 * d
  · subst j
    exact genericHilbertAt_of_genericEndpoint (hN K n (by omega) r (by omega))
      (hT n (by omega) r (by omega))
  · exact (genericHilbertThrough_iff _).mp hprefix j (by omega)

end Froberg
