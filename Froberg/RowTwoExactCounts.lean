import Froberg.RowTwoAsymptotic
import Froberg.ExactOuterLimit

/-! The row-two convolution witness for the exact Section 5 counts. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology
variable {K : Type*} [Field K] [Infinite K]

theorem eventually_row_two_of_exact_conditions {d : ℕ} (hd : 3 ≤ d) :
    ∀ᶠ h : ℕ in atTop, ∀ (k lo : ℕ) (upper : Bool) (a f e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop, ExactCountConditions d k h lo n (a n) (f n) (e n) upper) →
      ∀ᶠ n : ℕ in atTop, RowTwoTargetWitness K (d-1) h n (f n) (e n) := by
  filter_upwards [eventually_row_two_exact (K := K) hd] with h hh
  intro k lo upper a f e hc
  have hf := exact_conditions_outer_limit hd upper a f e hc
  filter_upwards [hh f hf,hc] with n hn hcn
  exact hn (e n) hcn.quadratic_lower

end Froberg
