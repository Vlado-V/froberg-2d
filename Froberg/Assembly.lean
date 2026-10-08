import Froberg.PrefixTheorem
import Froberg.QuadraticEndpoint
import Froberg.LinearBase
import Froberg.EquivariantReduction
import Froberg.Truncation

/-! Assembly of the endpoint induction, the lower-degree theorem, and the
common nonempty open in the precise statement of the manuscript. -/
noncomputable section
namespace Froberg
variable {K : Type} [Field K] [CharZero K]

theorem mainStatement_of_eventual_endpoints
    (hend : ∀ d : ℕ, 2 ≤ d → ∃ N : ℕ, 1 ≤ N ∧ ∀ n, N ≤ n →
      ∀ r, r ≤ (n + d - 1).choose d → GenericEndpoint K n d r) :
    MainStatement K := by
  intro d hd
  by_cases hd1 : d = 1
  · subst d
    exact degree_one_base
  have hd2 : 2 ≤ d := by omega
  obtain ⟨N, hNpos, hN⟩ := hend d hd2
  obtain ⟨T, hT⟩ := exists_endpoint_truncation_threshold hd2
  refine ⟨max N (max T (prefixThreshold d)), by omega, fun n hn r => ?_⟩
  have hnpos : 0 < n := by omega
  by_cases hr : (n + d - 1).choose d ≤ r
  · exact genericHilbertThrough_of_many_generators hnpos (by omega) hr _
  have hprefix := genericHilbertThrough_prefix (K := K) (by omega : 0 < d)
    (show prefixThreshold d ≤ n by omega) r
  apply (genericHilbertThrough_iff _).mpr
  intro j hj
  by_cases heq : j = 2 * d
  · subst j
    exact genericHilbertAt_of_genericEndpoint (hN n (by omega) r (by omega))
      (hT n (by omega) r (by omega))
  · exact (genericHilbertThrough_iff _).mp hprefix j (by omega)

theorem eventual_endpoints_of_inductive_recurrence
    (hrec : ∀ d : ℕ, 3 ≤ d →
      (∃ N : ℕ, 1 ≤ N ∧ ∀ n, N ≤ n → ∀ r, r ≤ (n + (d - 1) - 1).choose (d - 1) →
        GenericEndpoint K n (d - 1) r) →
      ∃ h start : ℕ, 0 < h ∧ ∀ n, start ≤ n → criticalDefect K (n + h) d ≤ criticalDefect K n d) :
    ∀ d : ℕ, 2 ≤ d → ∃ N : ℕ, 1 ≤ N ∧ ∀ n, N ≤ n →
      ∀ r, r ≤ (n + d - 1).choose d → GenericEndpoint K n d r := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base =>
      refine ⟨1, le_rfl, fun n hn r hr => ?_⟩
      exact genericEndpoint_quadratic hn (by simpa using hr)
  | succ d hd ih =>
      obtain ⟨h, start, hh, hs⟩ := hrec (d + 1) (by omega) (by simpa using ih)
      exact genericEndpoints_eventually_of_recurrence
        (d := d + 1) (start := start) (by omega) hh hs

theorem mainStatement_of_inductive_recurrence
    (hrec : ∀ d : ℕ, 3 ≤ d →
      (∃ N : ℕ, 1 ≤ N ∧ ∀ n, N ≤ n → ∀ r, r ≤ (n + (d - 1) - 1).choose (d - 1) →
        GenericEndpoint K n (d - 1) r) →
      ∃ h start : ℕ, 0 < h ∧ ∀ n, start ≤ n → criticalDefect K (n + h) d ≤ criticalDefect K n d) :
    MainStatement K :=
  mainStatement_of_eventual_endpoints (eventual_endpoints_of_inductive_recurrence hrec)

end Froberg
