module

public import Quartic.ProfileCertificate.Data

@[expose] public section

/-!
# Verified integral profile inequalities

This proves the numerical inequality `pc:profileineq` for every integral profile
in all 26 configurations with child dimension 28 through 40. The two endpoints
are the independently sign-certified counts from `FiniteCounts`. Interpreting
`Phi` and `Cell` as geometric image and stratum bounds is a separate obligation.
The expensive kernel checks are cached in `ProfileCertificate.Data`.
-/

namespace Quartic.ProfileCertificate

open Quartic.Counts Quartic.FiniteCounts

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- All 26 configurations, linked to the independently verified endpoint table. -/
theorem all_configurations_verified (index : Fin 13) (upper : Bool) :
    let m := (index : ℕ) + 28
    ConfigurationValid m (upperEndpoint m) (mixedCount m upper) := by
  fin_cases index <;> cases upper
  · exact configuration_28_lower
  · exact configuration_28_upper
  · exact configuration_29_lower
  · exact configuration_29_upper
  · exact configuration_30_lower
  · exact configuration_30_upper
  · exact configuration_31_lower
  · exact configuration_31_upper
  · exact configuration_32_lower
  · exact configuration_32_upper
  · exact configuration_33_lower
  · exact configuration_33_upper
  · exact configuration_34_lower
  · exact configuration_34_upper
  · exact configuration_35_lower
  · exact configuration_35_upper
  · exact configuration_36_lower
  · exact configuration_36_upper
  · exact configuration_37_lower
  · exact configuration_37_upper
  · exact configuration_38_lower
  · exact configuration_38_upper
  · exact configuration_39_lower
  · exact configuration_39_upper
  · exact configuration_40_lower
  · exact configuration_40_upper

/-- The manuscript's integral profile inequality throughout its finite range.

The hypotheses specify exactly `0 ≤ i ≤ A`, `0 ≤ n₃ ≤ n₂ ≤ n₁ ≤ w`,
and `0 < d < a`; lower bounds of zero are built into the natural number types.
The outer dimension on the right is the original Euler count `Counts.j`.
-/
theorem profile_inequality (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40)
    (upper : Bool) (i n₁ n₂ n₃ : ℕ)
    (hi : i ≤ coreA (mixedCount m upper))
    (hn₁ : n₁ ≤ freeW m (mixedCount m upper))
    (hn₂ : n₂ ≤ n₁) (hn₃ : n₃ ≤ n₂)
    (hdlo : 0 < profileDim i n₁ n₂ n₃)
    (hdhi : profileDim i n₁ n₂ n₃ < totalA m (mixedCount m upper)) :
    let q := upperEndpoint m
    let c := mixedCount m upper
    let d := profileDim i n₁ n₂ n₃
    (q : ℤ) * (d : ℤ) + Cell m c i n₁ n₂ n₃ +
      min (((c : ℤ) + 4) * (d : ℤ)) (j m q c) ≤ Phi m c i n₁ n₂ n₃ := by
  have hconfig := all_configurations_verified ⟨m - 28, by omega⟩ upper
  have hm : m - 28 + 28 = m := by omega
  simp only [hm] at hconfig
  have h := hconfig ⟨i, by omega⟩ ⟨n₁, by omega⟩
    ⟨n₂, by change n₂ < n₁ + 1; omega⟩
    ⟨n₃, by change n₃ < n₂ + 1; omega⟩
    (by change profileDim i n₁ n₂ n₃ ≠ 0; omega)
    (by change profileDim i n₁ n₂ n₃ ≠ totalA m (mixedCount m upper); omega)
  simpa only [ProfileBound, outerJ_eq_j] using h

end Quartic.ProfileCertificate
