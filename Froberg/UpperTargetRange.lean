module

public import Froberg.UpperTargetOpen

@[expose] public section

/-! The high-target conclusion depends only on the actual generator span. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type} [Field K] {h m d r s : ℕ}

theorem upperTargetMap_surjective_of_range
    (q : Fin r → Forms K (h+m) d) (p : Fin s → Forms K (h+m) d)
    (he : Set.range (fun i => (q i).val)=Set.range (fun i => (p i).val))
    (hq : Function.Surjective (upperTargetMap q)) :
    Function.Surjective (upperTargetMap p) := by
  have hr : (endpointMultiplication q).range=(endpointMultiplication p).range := by
    rw [range_endpointMultiplication,range_endpointMultiplication,he]
  apply LinearMap.range_eq_top.mp
  rw [upperTargetMap,LinearMap.range_comp,←hr]
  simpa only [upperTargetMap,LinearMap.range_comp] using LinearMap.range_eq_top.mpr hq

end Froberg
