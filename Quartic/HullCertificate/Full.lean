import Quartic.HullCertificate.Rational

/-! The full source dimension in the outer scalar inequality. -/

namespace Quartic.HullCertificate

open Quartic.Counts Quartic.FiniteCounts Quartic.ProfileCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exact integer check of the outer inequality at the full weak vertex. -/
theorem full_vertex_outer_verified :
    ∀ index : Fin 190, ∀ upper : Bool,
      let m := (index : ℕ) + 130
      let q := upperEndpoint m
      let c := mixedCount m upper
      6 * (q : ℤ) * (totalA m c : ℤ) ≤ (vertex m c 3 7).y := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- At `d=a` the rational weak-vertex image is at least `qa`. -/
theorem full_vertex_outer (m : ℕ) (hmlo : 130 ≤ m) (hmhi : m ≤ 319) (upper : Bool) :
    let q := upperEndpoint m
    let c := mixedCount m upper
    (q : ℚ) * (totalA m c : ℚ) ≤
      weakImage (coreA c) (coreB c) (freeW m c)
        (b2 (freeW m c)) (b3 (freeW m c)) 1 3 := by
  have h := full_vertex_outer_verified ⟨m - 130, by omega⟩ upper
  have hm : m - 130 + 130 = m := by omega
  simp only [hm] at h
  have hq : (6 : ℚ) * (upperEndpoint m : ℚ) * (totalA m (mixedCount m upper) : ℚ) ≤
      ((vertex m (mixedCount m upper) 3 7).y : ℚ) := by exact_mod_cast h
  have hv := vertex_image m (mixedCount m upper) 3 ⟨7, by decide⟩
  norm_num only [Fin.val_mk, Nat.reduceMod, Nat.reduceAdd, Nat.reduceDiv,
    (show knot 4 = 6 from rfl), Nat.cast_ofNat, div_self (by norm_num : (6 : ℚ) ≠ 0)] at hv
  dsimp
  linarith

end Quartic.HullCertificate
