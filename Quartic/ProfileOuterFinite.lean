import Quartic.ProfileCertificate

/-! # The finite outer profile budget, including the full source profile -/
set_option maxRecDepth 10000
namespace Quartic.ProfileOuterFinite
open ProfileCertificate FiniteCounts

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The full-profile budget in all 26 small endpoint configurations. -/
theorem full_profile_verified : ∀ k : Fin 13,∀ upper : Bool,
    let m := k.val+28
    let c := mixedCount m upper
    (upperEndpoint m:ℤ)*(totalA m c:ℤ)+Cell m c (coreA c) (freeW m c) (freeW m c) (freeW m c) ≤
      Phi m c (coreA c) (freeW m c) (freeW m c) (freeW m c) := by
  decide +kernel

/-- All positive profiles, including the full one, satisfy the outer incidence budget. -/
theorem profile_outer_bound (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40) (upper : Bool)
    (i n₁ n₂ n₃ : ℕ) (hi : i ≤ coreA (mixedCount m upper))
    (hn₁ : n₁ ≤ freeW m (mixedCount m upper)) (hn₂ : n₂ ≤ n₁) (hn₃ : n₃ ≤ n₂)
    (hdlo : 0 < profileDim i n₁ n₂ n₃)
    (hdhi : profileDim i n₁ n₂ n₃ ≤ totalA m (mixedCount m upper)) :
    (upperEndpoint m:ℤ)*(profileDim i n₁ n₂ n₃:ℤ)+
      Cell m (mixedCount m upper) i n₁ n₂ n₃ ≤ Phi m (mixedCount m upper) i n₁ n₂ n₃ := by
  by_cases hlt : profileDim i n₁ n₂ n₃ < totalA m (mixedCount m upper)
  · have h := profile_inequality m hmlo hmhi upper i n₁ n₂ n₃ hi hn₁ hn₂ hn₃ hdlo hlt
    have hj := (structural_dimension_signs m hmlo (by omega) upper).1
    have hn : 0 ≤ min (((mixedCount m upper:ℤ)+4)*(profileDim i n₁ n₂ n₃:ℤ))
        (Counts.j m (upperEndpoint m) (mixedCount m upper)) := by
      apply le_min
      · positivity
      · omega
    omega
  · have hd : profileDim i n₁ n₂ n₃=totalA m (mixedCount m upper) := by omega
    have hieq : i=coreA (mixedCount m upper) := by unfold profileDim totalA at hd; omega
    have hn1eq : n₁=freeW m (mixedCount m upper) := by unfold profileDim totalA at hd; omega
    have hn2eq : n₂=freeW m (mixedCount m upper) := by unfold profileDim totalA at hd; omega
    have hn3eq : n₃=freeW m (mixedCount m upper) := by unfold profileDim totalA at hd; omega
    rw [hd,hieq,hn1eq,hn2eq,hn3eq]
    have h := full_profile_verified ⟨m-28,by omega⟩ upper
    have he : m-28+28=m := by omega
    simpa only [he] using h

end Quartic.ProfileOuterFinite
