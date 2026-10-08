import Froberg.PreparedCountIdentities
import Froberg.ExactOuterLimit
import Froberg.OddScalarParameters

/-! The actual complete scalar background has the prescribed density for
all non-top odd quotient-growth estimates simultaneously. -/
noncomputable section
namespace Froberg
open Filter Module
variable {K : Type*} [Field K] [Infinite K] {h d k lo : ℕ}

theorem eventually_counted_odd_scalar_growth (hd : 3≤d) (hh : 0<h)
    (upper : Bool) (a f q : ℕ → ℕ)
    (hcounts : ∀ᶠ m in atTop,ExactCountConditions d k h lo m (a m) (f m) (q m) upper) :
    ∀ᶠ m : ℕ in atTop,HasOddScalarLayersOpen K h m d (f m)
      (upperCount m d) ⌊oddRowExtraDensity d*(m : ℝ)^d⌋₊ := by
  apply eventually_odd_scalar_layers_open hd hh (fun m => upperCount m d) f
  · exact upperCount_normalized_limit (by omega)
  · exact exact_conditions_outer_limit hd upper a f q hcounts

theorem eventually_prepared_odd_scalar_growth (hd : 3≤d) (hh : 0<h)
    (upper : Bool) (a f q : ℕ → ℕ) (extra : ℕ)
    (hcounts : ∀ᶠ m in atTop,ExactCountConditions d k h lo m (a m) (f m) (q m) upper) :
    ∀ᶠ m : ℕ in atTop,HasOddScalarLayersOpen K h m d (f m)
      (preparedScalarCount d h m (q m)+extra) ⌊oddRowExtraDensity d*(m : ℝ)^d⌋₊ := by
  apply eventually_odd_scalar_layers_open hd hh
    (fun m => preparedScalarCount d h m (q m)+extra) f
  · apply preparedScalarCount_normalized_limit hd h extra q
    exact hcounts.mono fun m hm => hm.quadratic_upper
  · exact exact_conditions_outer_limit hd upper a f q hcounts

end Froberg
