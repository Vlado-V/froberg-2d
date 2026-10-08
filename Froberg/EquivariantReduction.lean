import Froberg.GeometricReduction
import Froberg.GenericDivisibility

/-! Applying the proved equivariant divisibility theorem to the arithmetic
vanishing argument. Only the geometric recurrence remains as an input. -/
noncomputable section
namespace Froberg
variable {K : Type} [Field K] [CharZero K]

theorem criticalDefect_eventually_zero_of_recurrence {d h start : ℕ}
    (hd : 2 ≤ d) (hh : 0 < h)
    (hstep : ∀ n, start ≤ n → criticalDefect K (n + h) d ≤ criticalDefect K n d) :
    ∃ N : ℕ, ∀ n, N ≤ n → criticalDefect K n d = 0 := by
  apply criticalDefect_eventually_zero_of_recurrence_and_divisibility
    (start := max start 1) hd hh (fun n hn => hstep n (by omega))
  intro n hn r hr
  have hn0 : 0 < n := by omega
  exact ⟨genericHomology_divisibility hn0 hr, genericCokernel_divisibility hn0⟩

theorem genericEndpoints_eventually_of_recurrence {d h start : ℕ}
    (hd : 2 ≤ d) (hh : 0 < h)
    (hstep : ∀ n, start ≤ n → criticalDefect K (n + h) d ≤ criticalDefect K n d) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n, N ≤ n → ∀ r, r ≤ (n + d - 1).choose d →
      GenericEndpoint K n d r := by
  apply genericEndpoints_eventually_of_recurrence_and_divisibility
    (start := max start 1) hd hh (fun n hn => hstep n (by omega))
  intro n hn r hr
  have hn0 : 0 < n := by omega
  exact ⟨genericHomology_divisibility hn0 hr, genericCokernel_divisibility hn0⟩

end Froberg
