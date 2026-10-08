import Froberg.ProjectedTopAugmentation
import Froberg.ExactOuterLimit
import Froberg.UpperEndpointConvolution

/-! The exact rounded generator counts satisfy the top-row open conditions. -/
noncomputable section
namespace Froberg
open Filter Module Quartic
variable {K : Type*} [Field K] [Infinite K] {h e b k lo : ℕ}

theorem eventually_counted_top_growth (hh : 0 < h) (he : 2≤e) (hb : 0 < b)
    (P : Forms K h (1+e) →ₗ[K] (Fin b → K))
    (hP : ∀ L : Submodule K (Forms K h e),b*finrank K L≤
      finrank K (Forms K h e)*
        finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := e)) L).map P))
    (hratio : (h : ℝ)/(2*((1+e : ℕ) : ℝ))≤(b : ℝ)/((h+e-1).choose e : ℝ))
    (upper : Bool) (a f q : ℕ → ℕ)
    (hcounts : ∀ᶠ m in atTop,
      ExactCountConditions (1+e) k h lo m (a m) (f m) (q m) upper) :
    ∀ᶠ m : ℕ in atTop,
      ProjectedTopGrowthOpen P m (f m) (upperCount m (1+e)) (scalarReserveCount (1+e) m) := by
  apply eventually_projected_top_growth_open hh he hb P hP hratio f
    (fun m => upperCount m (1+e))
  · simpa only [show 1+e-1=e by omega] using
      exact_conditions_outer_limit (show 3≤1+e by omega) upper a f q hcounts
  · exact upperCount_normalized_limit (by omega)

end Froberg
