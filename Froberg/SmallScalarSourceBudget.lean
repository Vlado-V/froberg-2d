module

public import Froberg.SmallDegreeCapacities
public import Froberg.CapacityProductIdentity
public import Froberg.ScalarSeparationAsymptotic

@[expose] public section

/-! The two-fifths retained scalar-source incidence budget in Appendix E. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem scalar_incidence_gap_of_choose {d e : ℕ}
    (hgap : ((e+d).choose e : ℝ)*criticalRatio d < 2/5) :
    5*(e.factorial : ℝ)⁻¹*(criticalRatio d/(d.factorial : ℝ)) <
      2*((e+d).factorial : ℝ)⁻¹ := by
  have ht : (0 : ℝ)<(e+d).factorial := by positivity
  apply (mul_lt_mul_iff_left₀ ht).mp
  have hc : ((e+d).choose e : ℝ) = ((e+d).factorial : ℝ)/
      ((e.factorial : ℝ)*(d.factorial : ℝ)) := by
    simpa only [Nat.add_sub_cancel_left] using choose_real_factorial (Nat.le_add_right e d)
  rw [hc] at hgap
  field_simp [factorial_real_ne_zero] at hgap ⊢
  nlinarith

theorem eventually_small_scalar_source_budget {d R : ℕ}
    (hd : 3≤d) (hd8 : d≤8) (hR : R=4 ∨ R=6 ∨ R=8) (hRd : R≤d)
    (q : ℕ → ℕ)
    (hq : Tendsto (fun n : ℕ => (q n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ)))) :
    ∀ᶠ n : ℕ in atTop,
      5*(n+(d-R)-1).choose (d-R)*((n+(d-R)-1).choose (d-R)+q n) ≤
        2*(n+(d-R+d)-1).choose (d-R+d) := by
  apply eventually_scalar_incidence_budget (by rcases hR with rfl | rfl | rfl <;> omega) q _ hq
  apply scalar_incidence_gap_of_choose
  simpa only [show d-R+d=2*d-R by omega] using small_scalar_source_capacity hd hd8 hR hRd

end Froberg
