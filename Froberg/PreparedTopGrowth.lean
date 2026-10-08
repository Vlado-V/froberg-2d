import Froberg.PreparedCountIdentities
import Froberg.ExactOuterLimit
import Froberg.TopQuotientGrowth

/-! Top-row growth for the actual scalar background: the old scalar tuple,
every scalar shift attached to an even layer, and fixed appended slots. -/
noncomputable section
namespace Froberg
open Filter Module Quartic
variable {K : Type*} [Field K] [Infinite K] {h e b k lo : ℕ}

theorem eventually_prepared_top_growth (hh : 0<h) (he : 2≤e) (hb : 0<b)
    (P : Forms K h (1+e) →ₗ[K] (Fin b → K))
    (hP : ∀ L : Submodule K (Forms K h e),b*finrank K L≤
      finrank K (Forms K h e)*
        finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := e)) L).map P))
    (hratio : (h : ℝ)/(2*((1+e : ℕ) : ℝ))≤(b : ℝ)/((h+e-1).choose e : ℝ))
    (upper : Bool) (a f q : ℕ → ℕ) (extra : ℕ)
    (hcounts : ∀ᶠ m in atTop,
      ExactCountConditions (1+e) k h lo m (a m) (f m) (q m) upper) :
    ∀ᶠ m : ℕ in atTop,ProjectedTopGrowthOpen P m (f m)
      (preparedScalarCount (1+e) h m (q m)+extra) (scalarReserveCount (1+e) m) := by
  apply eventually_projected_top_growth_open hh he hb P hP hratio f
    (fun m => preparedScalarCount (1+e) h m (q m)+extra)
  · simpa only [show 1+e-1=e by omega] using
      exact_conditions_outer_limit (show 3≤1+e by omega) upper a f q hcounts
  · apply preparedScalarCount_normalized_limit (show 3≤1+e by omega) h extra q
    exact hcounts.mono fun m hm => hm.quadratic_upper

end Froberg
