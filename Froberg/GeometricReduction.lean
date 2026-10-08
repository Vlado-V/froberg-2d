import Froberg.GenericMonotonicity
import Froberg.CriticalApproximation
import Froberg.ArithmeticVanishing

/-! The arithmetic conclusion applied to the actual generic polynomial
defects. The two remaining inputs are explicitly the geometric recurrence
and equivariant divisibility; neither is folded into a definition. -/
noncomputable section
namespace Froberg

variable {K : Type} [Field K] [CharZero K]

omit [CharZero K] in
/-- For actual generic endpoint dimensions, the geometric recurrence and
divisibility imply eventual vanishing of both critical defects. The critical
root approximation and all arithmetic selection arguments are proved inputs. -/
theorem criticalDefect_eventually_zero_of_recurrence_and_divisibility
    {d h start : ℕ} (hd : 2 ≤ d) (hh : 0 < h)
    (hstep : ∀ n, start ≤ n → criticalDefect K (n + h) d ≤ criticalDefect K n d)
    (hdiv : ∀ n, start ≤ n → ∀ r, r ≤ (n + d - 1).choose d →
      Nat.gcd n (d * r) ∣ (2 * d) * genericHomology K n d r ∧
      Nat.gcd n (d * r) ∣ (2 * d) * genericCokernel K n d r) :
    ∃ N : ℕ, ∀ n, N ≤ n → criticalDefect K n d = 0 := by
  obtain ⟨P, hPdeg, _, hI, happ⟩ := exists_critical_polynomial_approximation hd
  obtain ⟨N, hN⟩ := arithmetic_eventual_vanishing d h (max start 1)
    (by omega) hh P (by omega) hI (fun n => kappa n d) happ
    ⟨1, fun n hn => (kappa_bounds (by omega : 0 < n) d).1.le⟩
    (fun n => genericHomology K n d (lowerCount n d))
    (fun n => genericCokernel K n d (upperCount n d))
    (fun n hn => hstep n (by omega))
    (fun n hn => (hdiv n (by omega) _
      (lowerCount_le_monomial_count (by omega : 0 < n) d)).1)
    (fun n hn => (hdiv n (by omega) _
      (upperCount_le_monomial_count (by omega : 0 < n) d)).2)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hH, hC⟩ := hN n hn
  simp only [criticalDefect, hH, hC, max_self]

/-- The same two geometric inputs imply all admissible generic endpoint
statements for sufficiently many variables. -/
theorem genericEndpoints_eventually_of_recurrence_and_divisibility
    {d h start : ℕ} (hd : 2 ≤ d) (hh : 0 < h)
    (hstep : ∀ n, start ≤ n → criticalDefect K (n + h) d ≤ criticalDefect K n d)
    (hdiv : ∀ n, start ≤ n → ∀ r, r ≤ (n + d - 1).choose d →
      Nat.gcd n (d * r) ∣ (2 * d) * genericHomology K n d r ∧
      Nat.gcd n (d * r) ∣ (2 * d) * genericCokernel K n d r) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n, N ≤ n → ∀ r, r ≤ (n + d - 1).choose d →
      GenericEndpoint K n d r := by
  obtain ⟨N, hN⟩ := criticalDefect_eventually_zero_of_recurrence_and_divisibility hd hh hstep hdiv
  refine ⟨max N 1, by omega, fun n hn => ?_⟩
  exact genericEndpoints_of_criticalDefect_zero (by norm_num) (by omega) (hN n (by omega))

end Froberg
