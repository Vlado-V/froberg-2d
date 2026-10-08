import Froberg.ShiftedSmallCapacities
import Froberg.ProductCapacityParameters

/-! The strong cubic/quartic quadratic witness accommodates the literal
integer E count at total size 2v+z and fixed appended private slots. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem eventually_strong_quadratic_capacity_shift {d : ℕ} (hd : d=3 ∨ d=4) :
    ∀ᶠ h : ℕ in atTop,∀ z extra : ℕ,∀ᶠ v : ℕ in atTop,∀ r : ℕ,
      (r : ℝ)<countBeta d*(h : ℝ)^2*((2*v+z : ℕ) : ℝ)^(d-2) →
      r+extra≤(2*(h/2).choose 2-deletedTargetCount d h)*
        (if d=3 then v else v.choose (d-2)/2) := by
  have hh : ∀ᶠ h : ℕ in atTop,∀ z extra : ℕ,∀ᶠ n : ℕ in atTop,
      ⌈countBeta d*(h : ℝ)^2*((n+z : ℕ) : ℝ)^(d-2)⌉₊+extra≤
        (2*(h/2).choose 2-deletedTargetCount d h)*
          (if d=3 then n/2 else (n/2).choose (d-2)/2) := by
    rcases hd with rfl | rfl
    · simpa only [show 3-2=1 by omega,pow_one,ite_true] using
        eventually_strong_cubic_diagonal_capacity_shift
    · simpa only [show 4-2=2 by omega,if_neg (show (4 : ℕ)≠3 by decide)] using
        eventually_strong_quartic_diagonal_capacity_shift
  filter_upwards [hh] with h hh
  intro z extra
  filter_upwards [PreparedParameters.tendsto_twice_nat.eventually (hh z extra)] with v hv
  intro r hr
  have hc : r≤⌈countBeta d*(h : ℝ)^2*((2*v+z : ℕ) : ℝ)^(d-2)⌉₊ := by
    exact_mod_cast hr.le.trans (Nat.le_ceil _)
  exact (Nat.add_le_add_right hc extra).trans (by simpa only [show 2*v/2=v by omega] using hv)

end Froberg
