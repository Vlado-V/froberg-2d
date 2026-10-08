import Quartic.SharpCertificate.Rational

/-! The full source dimension in the sharp outer inequality. -/

namespace Quartic.SharpCertificate

open Quartic.Counts Quartic.FiniteCounts Quartic.ProfileCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The exact full-source outer inequality for all 178 endpoint configurations. -/
theorem full_source_outer_verified :
    ∀ index : Fin 89, ∀ upper : Bool,
      let m := (index : ℕ) + 41
      let q := upperEndpoint m
      let c := mixedCount m upper
      edgeScale 5 * (q : ℤ) * (totalA m c : ℤ) ≤
        (edgePolynomial (parameters m c (coreA c)) 5).eval (totalA m c) := by
  decide +kernel

/-- At `d=a`, the full sharp source satisfies the outer incidence inequality. -/
theorem full_source_outer (m : ℕ) (hmlo : 41 ≤ m) (hmhi : m ≤ 129) (upper : Bool) :
    let q := upperEndpoint m
    let c := mixedCount m upper
    (q : ℚ) * (totalA m c : ℚ) ≤
      sharpEdge (parameters m c (coreA c)) 5 (totalA m c) := by
  have h := full_source_outer_verified ⟨m - 41, by omega⟩ upper
  have hm : m - 41 + 41 = m := by omega
  simp only [hm] at h
  dsimp
  rw [sharpEdge_eq_quotient]
  have hD : (0 : ℚ) < edgeScale 5 := by exact_mod_cast edgeScale_pos 5
  apply (le_div_iff₀ hD).2
  have hq : (edgeScale 5 : ℚ) * (upperEndpoint m : ℚ) *
      (totalA m (mixedCount m upper) : ℚ) ≤
      ((edgePolynomial (parameters m (mixedCount m upper) (coreA (mixedCount m upper))) 5).eval
        (totalA m (mixedCount m upper)) : ℚ) := by exact_mod_cast h
  nlinarith only [hq]

/-- The chosen full edge point is exactly the full three-layer profile. -/
theorem sharpEdge_full_profile (m c : ℕ) :
    sharpEdge (parameters m c (coreA c)) 5 (totalA m c) =
      sharpProfile (parameters m c (coreA c)) (freeW m c) (freeW m c) (freeW m c) := by
  have hz : edgeIntermediate (parameters m c (coreA c)) 5 (totalA m c) = (freeW m c : ℚ) := by
    norm_num [edgeIntermediate, edgeLeft, edgeRight, edgeWidth, parameters, totalA]
    ring
  simp only [sharpEdge, hz]
  norm_num [edgeLeft, edgeRight, edgeLayer, parameters]

/-- The full three-layer sharp expression satisfies the outer inequality. -/
theorem full_profile_outer (m : ℕ) (hmlo : 41 ≤ m) (hmhi : m ≤ 129) (upper : Bool) :
    let q := upperEndpoint m
    let c := mixedCount m upper
    (q : ℚ) * (totalA m c : ℚ) ≤
      sharpProfile (parameters m c (coreA c)) (freeW m c) (freeW m c) (freeW m c) := by
  have h := full_source_outer m hmlo hmhi upper
  simpa only [sharpEdge_full_profile] using h

end Quartic.SharpCertificate
