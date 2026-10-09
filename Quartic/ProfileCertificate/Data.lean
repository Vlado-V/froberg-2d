module

public import Quartic.ProfileCertificate.Core

@[expose] public section

/-! Numerical kernel checks. Each reduction fixes the outer core index,
so at most 2,600 layer profiles are checked at once. The original
configuration statements are assembled from these checked slices. -/

namespace Quartic.ProfileCertificate

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exactly the remaining binders of `ConfigurationValid` at a fixed `i`. -/
def ConfigurationSlice (m q c i : ℕ) : Prop :=
  ∀ n₁ : Fin (freeW m c + 1),
  ∀ n₂ : Fin (n₁.val + 1), ∀ n₃ : Fin (n₂.val + 1),
  profileDim i n₁ n₂ n₃ ≠ 0 →
  profileDim i n₁ n₂ n₃ ≠ totalA m c →
  ProfileBound m q c i n₁ n₂ n₃

instance (m q c i : ℕ) : Decidable (ConfigurationSlice m q c i) := by
  unfold ConfigurationSlice
  infer_instance

namespace Slices

theorem configuration_28_lower_i0 : ConfigurationSlice 28 87 13 0 := by
  decide +kernel

theorem configuration_28_lower_i1 : ConfigurationSlice 28 87 13 1 := by
  decide +kernel

theorem configuration_28_lower_i2 : ConfigurationSlice 28 87 13 2 := by
  decide +kernel

theorem configuration_28_lower_i3 : ConfigurationSlice 28 87 13 3 := by
  decide +kernel

theorem configuration_28_lower_i4 : ConfigurationSlice 28 87 13 4 := by
  decide +kernel

theorem configuration_28_lower_i5 : ConfigurationSlice 28 87 13 5 := by
  decide +kernel

theorem configuration_28_lower_i6 : ConfigurationSlice 28 87 13 6 := by
  decide +kernel

theorem configuration_28_lower_i7 : ConfigurationSlice 28 87 13 7 := by
  decide +kernel

theorem configuration_28_lower_i8 : ConfigurationSlice 28 87 13 8 := by
  decide +kernel

theorem configuration_28_lower_i9 : ConfigurationSlice 28 87 13 9 := by
  decide +kernel

theorem configuration_28_lower_i10 : ConfigurationSlice 28 87 13 10 := by
  decide +kernel

theorem configuration_28_lower_i11 : ConfigurationSlice 28 87 13 11 := by
  decide +kernel

theorem configuration_28_lower_i12 : ConfigurationSlice 28 87 13 12 := by
  decide +kernel

theorem configuration_28_lower_i13 : ConfigurationSlice 28 87 13 13 := by
  decide +kernel

theorem configuration_28_lower_i14 : ConfigurationSlice 28 87 13 14 := by
  decide +kernel

theorem configuration_28_lower_i15 : ConfigurationSlice 28 87 13 15 := by
  decide +kernel

theorem configuration_28_lower_i16 : ConfigurationSlice 28 87 13 16 := by
  decide +kernel

theorem configuration_28_lower_i17 : ConfigurationSlice 28 87 13 17 := by
  decide +kernel

theorem configuration_28_lower_i18 : ConfigurationSlice 28 87 13 18 := by
  decide +kernel

theorem configuration_28_lower_i19 : ConfigurationSlice 28 87 13 19 := by
  decide +kernel

theorem configuration_28_lower_i20 : ConfigurationSlice 28 87 13 20 := by
  decide +kernel

theorem configuration_28_upper_i0 : ConfigurationSlice 28 87 14 0 := by
  decide +kernel

theorem configuration_28_upper_i1 : ConfigurationSlice 28 87 14 1 := by
  decide +kernel

theorem configuration_28_upper_i2 : ConfigurationSlice 28 87 14 2 := by
  decide +kernel

theorem configuration_28_upper_i3 : ConfigurationSlice 28 87 14 3 := by
  decide +kernel

theorem configuration_28_upper_i4 : ConfigurationSlice 28 87 14 4 := by
  decide +kernel

theorem configuration_28_upper_i5 : ConfigurationSlice 28 87 14 5 := by
  decide +kernel

theorem configuration_28_upper_i6 : ConfigurationSlice 28 87 14 6 := by
  decide +kernel

theorem configuration_28_upper_i7 : ConfigurationSlice 28 87 14 7 := by
  decide +kernel

theorem configuration_28_upper_i8 : ConfigurationSlice 28 87 14 8 := by
  decide +kernel

theorem configuration_28_upper_i9 : ConfigurationSlice 28 87 14 9 := by
  decide +kernel

theorem configuration_28_upper_i10 : ConfigurationSlice 28 87 14 10 := by
  decide +kernel

theorem configuration_28_upper_i11 : ConfigurationSlice 28 87 14 11 := by
  decide +kernel

theorem configuration_28_upper_i12 : ConfigurationSlice 28 87 14 12 := by
  decide +kernel

theorem configuration_28_upper_i13 : ConfigurationSlice 28 87 14 13 := by
  decide +kernel

theorem configuration_28_upper_i14 : ConfigurationSlice 28 87 14 14 := by
  decide +kernel

theorem configuration_28_upper_i15 : ConfigurationSlice 28 87 14 15 := by
  decide +kernel

theorem configuration_28_upper_i16 : ConfigurationSlice 28 87 14 16 := by
  decide +kernel

theorem configuration_28_upper_i17 : ConfigurationSlice 28 87 14 17 := by
  decide +kernel

theorem configuration_28_upper_i18 : ConfigurationSlice 28 87 14 18 := by
  decide +kernel

theorem configuration_28_upper_i19 : ConfigurationSlice 28 87 14 19 := by
  decide +kernel

theorem configuration_28_upper_i20 : ConfigurationSlice 28 87 14 20 := by
  decide +kernel

theorem configuration_28_upper_i21 : ConfigurationSlice 28 87 14 21 := by
  decide +kernel

theorem configuration_28_upper_i22 : ConfigurationSlice 28 87 14 22 := by
  decide +kernel

theorem configuration_29_lower_i0 : ConfigurationSlice 29 93 13 0 := by
  decide +kernel

theorem configuration_29_lower_i1 : ConfigurationSlice 29 93 13 1 := by
  decide +kernel

theorem configuration_29_lower_i2 : ConfigurationSlice 29 93 13 2 := by
  decide +kernel

theorem configuration_29_lower_i3 : ConfigurationSlice 29 93 13 3 := by
  decide +kernel

theorem configuration_29_lower_i4 : ConfigurationSlice 29 93 13 4 := by
  decide +kernel

theorem configuration_29_lower_i5 : ConfigurationSlice 29 93 13 5 := by
  decide +kernel

theorem configuration_29_lower_i6 : ConfigurationSlice 29 93 13 6 := by
  decide +kernel

theorem configuration_29_lower_i7 : ConfigurationSlice 29 93 13 7 := by
  decide +kernel

theorem configuration_29_lower_i8 : ConfigurationSlice 29 93 13 8 := by
  decide +kernel

theorem configuration_29_lower_i9 : ConfigurationSlice 29 93 13 9 := by
  decide +kernel

theorem configuration_29_lower_i10 : ConfigurationSlice 29 93 13 10 := by
  decide +kernel

theorem configuration_29_lower_i11 : ConfigurationSlice 29 93 13 11 := by
  decide +kernel

theorem configuration_29_lower_i12 : ConfigurationSlice 29 93 13 12 := by
  decide +kernel

theorem configuration_29_lower_i13 : ConfigurationSlice 29 93 13 13 := by
  decide +kernel

theorem configuration_29_lower_i14 : ConfigurationSlice 29 93 13 14 := by
  decide +kernel

theorem configuration_29_lower_i15 : ConfigurationSlice 29 93 13 15 := by
  decide +kernel

theorem configuration_29_lower_i16 : ConfigurationSlice 29 93 13 16 := by
  decide +kernel

theorem configuration_29_lower_i17 : ConfigurationSlice 29 93 13 17 := by
  decide +kernel

theorem configuration_29_lower_i18 : ConfigurationSlice 29 93 13 18 := by
  decide +kernel

theorem configuration_29_lower_i19 : ConfigurationSlice 29 93 13 19 := by
  decide +kernel

theorem configuration_29_lower_i20 : ConfigurationSlice 29 93 13 20 := by
  decide +kernel

theorem configuration_29_upper_i0 : ConfigurationSlice 29 93 14 0 := by
  decide +kernel

theorem configuration_29_upper_i1 : ConfigurationSlice 29 93 14 1 := by
  decide +kernel

theorem configuration_29_upper_i2 : ConfigurationSlice 29 93 14 2 := by
  decide +kernel

theorem configuration_29_upper_i3 : ConfigurationSlice 29 93 14 3 := by
  decide +kernel

theorem configuration_29_upper_i4 : ConfigurationSlice 29 93 14 4 := by
  decide +kernel

theorem configuration_29_upper_i5 : ConfigurationSlice 29 93 14 5 := by
  decide +kernel

theorem configuration_29_upper_i6 : ConfigurationSlice 29 93 14 6 := by
  decide +kernel

theorem configuration_29_upper_i7 : ConfigurationSlice 29 93 14 7 := by
  decide +kernel

theorem configuration_29_upper_i8 : ConfigurationSlice 29 93 14 8 := by
  decide +kernel

theorem configuration_29_upper_i9 : ConfigurationSlice 29 93 14 9 := by
  decide +kernel

theorem configuration_29_upper_i10 : ConfigurationSlice 29 93 14 10 := by
  decide +kernel

theorem configuration_29_upper_i11 : ConfigurationSlice 29 93 14 11 := by
  decide +kernel

theorem configuration_29_upper_i12 : ConfigurationSlice 29 93 14 12 := by
  decide +kernel

theorem configuration_29_upper_i13 : ConfigurationSlice 29 93 14 13 := by
  decide +kernel

theorem configuration_29_upper_i14 : ConfigurationSlice 29 93 14 14 := by
  decide +kernel

theorem configuration_29_upper_i15 : ConfigurationSlice 29 93 14 15 := by
  decide +kernel

theorem configuration_29_upper_i16 : ConfigurationSlice 29 93 14 16 := by
  decide +kernel

theorem configuration_29_upper_i17 : ConfigurationSlice 29 93 14 17 := by
  decide +kernel

theorem configuration_29_upper_i18 : ConfigurationSlice 29 93 14 18 := by
  decide +kernel

theorem configuration_29_upper_i19 : ConfigurationSlice 29 93 14 19 := by
  decide +kernel

theorem configuration_29_upper_i20 : ConfigurationSlice 29 93 14 20 := by
  decide +kernel

theorem configuration_29_upper_i21 : ConfigurationSlice 29 93 14 21 := by
  decide +kernel

theorem configuration_29_upper_i22 : ConfigurationSlice 29 93 14 22 := by
  decide +kernel

theorem configuration_30_lower_i0 : ConfigurationSlice 30 99 14 0 := by
  decide +kernel

theorem configuration_30_lower_i1 : ConfigurationSlice 30 99 14 1 := by
  decide +kernel

theorem configuration_30_lower_i2 : ConfigurationSlice 30 99 14 2 := by
  decide +kernel

theorem configuration_30_lower_i3 : ConfigurationSlice 30 99 14 3 := by
  decide +kernel

theorem configuration_30_lower_i4 : ConfigurationSlice 30 99 14 4 := by
  decide +kernel

theorem configuration_30_lower_i5 : ConfigurationSlice 30 99 14 5 := by
  decide +kernel

theorem configuration_30_lower_i6 : ConfigurationSlice 30 99 14 6 := by
  decide +kernel

theorem configuration_30_lower_i7 : ConfigurationSlice 30 99 14 7 := by
  decide +kernel

theorem configuration_30_lower_i8 : ConfigurationSlice 30 99 14 8 := by
  decide +kernel

theorem configuration_30_lower_i9 : ConfigurationSlice 30 99 14 9 := by
  decide +kernel

theorem configuration_30_lower_i10 : ConfigurationSlice 30 99 14 10 := by
  decide +kernel

theorem configuration_30_lower_i11 : ConfigurationSlice 30 99 14 11 := by
  decide +kernel

theorem configuration_30_lower_i12 : ConfigurationSlice 30 99 14 12 := by
  decide +kernel

theorem configuration_30_lower_i13 : ConfigurationSlice 30 99 14 13 := by
  decide +kernel

theorem configuration_30_lower_i14 : ConfigurationSlice 30 99 14 14 := by
  decide +kernel

theorem configuration_30_lower_i15 : ConfigurationSlice 30 99 14 15 := by
  decide +kernel

theorem configuration_30_lower_i16 : ConfigurationSlice 30 99 14 16 := by
  decide +kernel

theorem configuration_30_lower_i17 : ConfigurationSlice 30 99 14 17 := by
  decide +kernel

theorem configuration_30_lower_i18 : ConfigurationSlice 30 99 14 18 := by
  decide +kernel

theorem configuration_30_lower_i19 : ConfigurationSlice 30 99 14 19 := by
  decide +kernel

theorem configuration_30_lower_i20 : ConfigurationSlice 30 99 14 20 := by
  decide +kernel

theorem configuration_30_lower_i21 : ConfigurationSlice 30 99 14 21 := by
  decide +kernel

theorem configuration_30_lower_i22 : ConfigurationSlice 30 99 14 22 := by
  decide +kernel

theorem configuration_30_upper_i0 : ConfigurationSlice 30 99 15 0 := by
  decide +kernel

theorem configuration_30_upper_i1 : ConfigurationSlice 30 99 15 1 := by
  decide +kernel

theorem configuration_30_upper_i2 : ConfigurationSlice 30 99 15 2 := by
  decide +kernel

theorem configuration_30_upper_i3 : ConfigurationSlice 30 99 15 3 := by
  decide +kernel

theorem configuration_30_upper_i4 : ConfigurationSlice 30 99 15 4 := by
  decide +kernel

theorem configuration_30_upper_i5 : ConfigurationSlice 30 99 15 5 := by
  decide +kernel

theorem configuration_30_upper_i6 : ConfigurationSlice 30 99 15 6 := by
  decide +kernel

theorem configuration_30_upper_i7 : ConfigurationSlice 30 99 15 7 := by
  decide +kernel

theorem configuration_30_upper_i8 : ConfigurationSlice 30 99 15 8 := by
  decide +kernel

theorem configuration_30_upper_i9 : ConfigurationSlice 30 99 15 9 := by
  decide +kernel

theorem configuration_30_upper_i10 : ConfigurationSlice 30 99 15 10 := by
  decide +kernel

theorem configuration_30_upper_i11 : ConfigurationSlice 30 99 15 11 := by
  decide +kernel

theorem configuration_30_upper_i12 : ConfigurationSlice 30 99 15 12 := by
  decide +kernel

theorem configuration_30_upper_i13 : ConfigurationSlice 30 99 15 13 := by
  decide +kernel

theorem configuration_30_upper_i14 : ConfigurationSlice 30 99 15 14 := by
  decide +kernel

theorem configuration_30_upper_i15 : ConfigurationSlice 30 99 15 15 := by
  decide +kernel

theorem configuration_30_upper_i16 : ConfigurationSlice 30 99 15 16 := by
  decide +kernel

theorem configuration_30_upper_i17 : ConfigurationSlice 30 99 15 17 := by
  decide +kernel

theorem configuration_30_upper_i18 : ConfigurationSlice 30 99 15 18 := by
  decide +kernel

theorem configuration_30_upper_i19 : ConfigurationSlice 30 99 15 19 := by
  decide +kernel

theorem configuration_30_upper_i20 : ConfigurationSlice 30 99 15 20 := by
  decide +kernel

theorem configuration_30_upper_i21 : ConfigurationSlice 30 99 15 21 := by
  decide +kernel

theorem configuration_30_upper_i22 : ConfigurationSlice 30 99 15 22 := by
  decide +kernel

theorem configuration_30_upper_i23 : ConfigurationSlice 30 99 15 23 := by
  decide +kernel

theorem configuration_30_upper_i24 : ConfigurationSlice 30 99 15 24 := by
  decide +kernel

theorem configuration_31_lower_i0 : ConfigurationSlice 31 105 14 0 := by
  decide +kernel

theorem configuration_31_lower_i1 : ConfigurationSlice 31 105 14 1 := by
  decide +kernel

theorem configuration_31_lower_i2 : ConfigurationSlice 31 105 14 2 := by
  decide +kernel

theorem configuration_31_lower_i3 : ConfigurationSlice 31 105 14 3 := by
  decide +kernel

theorem configuration_31_lower_i4 : ConfigurationSlice 31 105 14 4 := by
  decide +kernel

theorem configuration_31_lower_i5 : ConfigurationSlice 31 105 14 5 := by
  decide +kernel

theorem configuration_31_lower_i6 : ConfigurationSlice 31 105 14 6 := by
  decide +kernel

theorem configuration_31_lower_i7 : ConfigurationSlice 31 105 14 7 := by
  decide +kernel

theorem configuration_31_lower_i8 : ConfigurationSlice 31 105 14 8 := by
  decide +kernel

theorem configuration_31_lower_i9 : ConfigurationSlice 31 105 14 9 := by
  decide +kernel

theorem configuration_31_lower_i10 : ConfigurationSlice 31 105 14 10 := by
  decide +kernel

theorem configuration_31_lower_i11 : ConfigurationSlice 31 105 14 11 := by
  decide +kernel

theorem configuration_31_lower_i12 : ConfigurationSlice 31 105 14 12 := by
  decide +kernel

theorem configuration_31_lower_i13 : ConfigurationSlice 31 105 14 13 := by
  decide +kernel

theorem configuration_31_lower_i14 : ConfigurationSlice 31 105 14 14 := by
  decide +kernel

theorem configuration_31_lower_i15 : ConfigurationSlice 31 105 14 15 := by
  decide +kernel

theorem configuration_31_lower_i16 : ConfigurationSlice 31 105 14 16 := by
  decide +kernel

theorem configuration_31_lower_i17 : ConfigurationSlice 31 105 14 17 := by
  decide +kernel

theorem configuration_31_lower_i18 : ConfigurationSlice 31 105 14 18 := by
  decide +kernel

theorem configuration_31_lower_i19 : ConfigurationSlice 31 105 14 19 := by
  decide +kernel

theorem configuration_31_lower_i20 : ConfigurationSlice 31 105 14 20 := by
  decide +kernel

theorem configuration_31_lower_i21 : ConfigurationSlice 31 105 14 21 := by
  decide +kernel

theorem configuration_31_lower_i22 : ConfigurationSlice 31 105 14 22 := by
  decide +kernel

theorem configuration_31_upper_i0 : ConfigurationSlice 31 105 15 0 := by
  decide +kernel

theorem configuration_31_upper_i1 : ConfigurationSlice 31 105 15 1 := by
  decide +kernel

theorem configuration_31_upper_i2 : ConfigurationSlice 31 105 15 2 := by
  decide +kernel

theorem configuration_31_upper_i3 : ConfigurationSlice 31 105 15 3 := by
  decide +kernel

theorem configuration_31_upper_i4 : ConfigurationSlice 31 105 15 4 := by
  decide +kernel

theorem configuration_31_upper_i5 : ConfigurationSlice 31 105 15 5 := by
  decide +kernel

theorem configuration_31_upper_i6 : ConfigurationSlice 31 105 15 6 := by
  decide +kernel

theorem configuration_31_upper_i7 : ConfigurationSlice 31 105 15 7 := by
  decide +kernel

theorem configuration_31_upper_i8 : ConfigurationSlice 31 105 15 8 := by
  decide +kernel

theorem configuration_31_upper_i9 : ConfigurationSlice 31 105 15 9 := by
  decide +kernel

theorem configuration_31_upper_i10 : ConfigurationSlice 31 105 15 10 := by
  decide +kernel

theorem configuration_31_upper_i11 : ConfigurationSlice 31 105 15 11 := by
  decide +kernel

theorem configuration_31_upper_i12 : ConfigurationSlice 31 105 15 12 := by
  decide +kernel

theorem configuration_31_upper_i13 : ConfigurationSlice 31 105 15 13 := by
  decide +kernel

theorem configuration_31_upper_i14 : ConfigurationSlice 31 105 15 14 := by
  decide +kernel

theorem configuration_31_upper_i15 : ConfigurationSlice 31 105 15 15 := by
  decide +kernel

theorem configuration_31_upper_i16 : ConfigurationSlice 31 105 15 16 := by
  decide +kernel

theorem configuration_31_upper_i17 : ConfigurationSlice 31 105 15 17 := by
  decide +kernel

theorem configuration_31_upper_i18 : ConfigurationSlice 31 105 15 18 := by
  decide +kernel

theorem configuration_31_upper_i19 : ConfigurationSlice 31 105 15 19 := by
  decide +kernel

theorem configuration_31_upper_i20 : ConfigurationSlice 31 105 15 20 := by
  decide +kernel

theorem configuration_31_upper_i21 : ConfigurationSlice 31 105 15 21 := by
  decide +kernel

theorem configuration_31_upper_i22 : ConfigurationSlice 31 105 15 22 := by
  decide +kernel

theorem configuration_31_upper_i23 : ConfigurationSlice 31 105 15 23 := by
  decide +kernel

theorem configuration_31_upper_i24 : ConfigurationSlice 31 105 15 24 := by
  decide +kernel

theorem configuration_32_lower_i0 : ConfigurationSlice 32 111 15 0 := by
  decide +kernel

theorem configuration_32_lower_i1 : ConfigurationSlice 32 111 15 1 := by
  decide +kernel

theorem configuration_32_lower_i2 : ConfigurationSlice 32 111 15 2 := by
  decide +kernel

theorem configuration_32_lower_i3 : ConfigurationSlice 32 111 15 3 := by
  decide +kernel

theorem configuration_32_lower_i4 : ConfigurationSlice 32 111 15 4 := by
  decide +kernel

theorem configuration_32_lower_i5 : ConfigurationSlice 32 111 15 5 := by
  decide +kernel

theorem configuration_32_lower_i6 : ConfigurationSlice 32 111 15 6 := by
  decide +kernel

theorem configuration_32_lower_i7 : ConfigurationSlice 32 111 15 7 := by
  decide +kernel

theorem configuration_32_lower_i8 : ConfigurationSlice 32 111 15 8 := by
  decide +kernel

theorem configuration_32_lower_i9 : ConfigurationSlice 32 111 15 9 := by
  decide +kernel

theorem configuration_32_lower_i10 : ConfigurationSlice 32 111 15 10 := by
  decide +kernel

theorem configuration_32_lower_i11 : ConfigurationSlice 32 111 15 11 := by
  decide +kernel

theorem configuration_32_lower_i12 : ConfigurationSlice 32 111 15 12 := by
  decide +kernel

theorem configuration_32_lower_i13 : ConfigurationSlice 32 111 15 13 := by
  decide +kernel

theorem configuration_32_lower_i14 : ConfigurationSlice 32 111 15 14 := by
  decide +kernel

theorem configuration_32_lower_i15 : ConfigurationSlice 32 111 15 15 := by
  decide +kernel

theorem configuration_32_lower_i16 : ConfigurationSlice 32 111 15 16 := by
  decide +kernel

theorem configuration_32_lower_i17 : ConfigurationSlice 32 111 15 17 := by
  decide +kernel

theorem configuration_32_lower_i18 : ConfigurationSlice 32 111 15 18 := by
  decide +kernel

theorem configuration_32_lower_i19 : ConfigurationSlice 32 111 15 19 := by
  decide +kernel

theorem configuration_32_lower_i20 : ConfigurationSlice 32 111 15 20 := by
  decide +kernel

theorem configuration_32_lower_i21 : ConfigurationSlice 32 111 15 21 := by
  decide +kernel

theorem configuration_32_lower_i22 : ConfigurationSlice 32 111 15 22 := by
  decide +kernel

theorem configuration_32_lower_i23 : ConfigurationSlice 32 111 15 23 := by
  decide +kernel

theorem configuration_32_lower_i24 : ConfigurationSlice 32 111 15 24 := by
  decide +kernel

theorem configuration_32_upper_i0 : ConfigurationSlice 32 111 16 0 := by
  decide +kernel

theorem configuration_32_upper_i1 : ConfigurationSlice 32 111 16 1 := by
  decide +kernel

theorem configuration_32_upper_i2 : ConfigurationSlice 32 111 16 2 := by
  decide +kernel

theorem configuration_32_upper_i3 : ConfigurationSlice 32 111 16 3 := by
  decide +kernel

theorem configuration_32_upper_i4 : ConfigurationSlice 32 111 16 4 := by
  decide +kernel

theorem configuration_32_upper_i5 : ConfigurationSlice 32 111 16 5 := by
  decide +kernel

theorem configuration_32_upper_i6 : ConfigurationSlice 32 111 16 6 := by
  decide +kernel

theorem configuration_32_upper_i7 : ConfigurationSlice 32 111 16 7 := by
  decide +kernel

theorem configuration_32_upper_i8 : ConfigurationSlice 32 111 16 8 := by
  decide +kernel

theorem configuration_32_upper_i9 : ConfigurationSlice 32 111 16 9 := by
  decide +kernel

theorem configuration_32_upper_i10 : ConfigurationSlice 32 111 16 10 := by
  decide +kernel

theorem configuration_32_upper_i11 : ConfigurationSlice 32 111 16 11 := by
  decide +kernel

theorem configuration_32_upper_i12 : ConfigurationSlice 32 111 16 12 := by
  decide +kernel

theorem configuration_32_upper_i13 : ConfigurationSlice 32 111 16 13 := by
  decide +kernel

theorem configuration_32_upper_i14 : ConfigurationSlice 32 111 16 14 := by
  decide +kernel

theorem configuration_32_upper_i15 : ConfigurationSlice 32 111 16 15 := by
  decide +kernel

theorem configuration_32_upper_i16 : ConfigurationSlice 32 111 16 16 := by
  decide +kernel

theorem configuration_32_upper_i17 : ConfigurationSlice 32 111 16 17 := by
  decide +kernel

theorem configuration_32_upper_i18 : ConfigurationSlice 32 111 16 18 := by
  decide +kernel

theorem configuration_32_upper_i19 : ConfigurationSlice 32 111 16 19 := by
  decide +kernel

theorem configuration_32_upper_i20 : ConfigurationSlice 32 111 16 20 := by
  decide +kernel

theorem configuration_32_upper_i21 : ConfigurationSlice 32 111 16 21 := by
  decide +kernel

theorem configuration_32_upper_i22 : ConfigurationSlice 32 111 16 22 := by
  decide +kernel

theorem configuration_32_upper_i23 : ConfigurationSlice 32 111 16 23 := by
  decide +kernel

theorem configuration_32_upper_i24 : ConfigurationSlice 32 111 16 24 := by
  decide +kernel

theorem configuration_32_upper_i25 : ConfigurationSlice 32 111 16 25 := by
  decide +kernel

theorem configuration_32_upper_i26 : ConfigurationSlice 32 111 16 26 := by
  decide +kernel

theorem configuration_33_lower_i0 : ConfigurationSlice 33 118 15 0 := by
  decide +kernel

theorem configuration_33_lower_i1 : ConfigurationSlice 33 118 15 1 := by
  decide +kernel

theorem configuration_33_lower_i2 : ConfigurationSlice 33 118 15 2 := by
  decide +kernel

theorem configuration_33_lower_i3 : ConfigurationSlice 33 118 15 3 := by
  decide +kernel

theorem configuration_33_lower_i4 : ConfigurationSlice 33 118 15 4 := by
  decide +kernel

theorem configuration_33_lower_i5 : ConfigurationSlice 33 118 15 5 := by
  decide +kernel

theorem configuration_33_lower_i6 : ConfigurationSlice 33 118 15 6 := by
  decide +kernel

theorem configuration_33_lower_i7 : ConfigurationSlice 33 118 15 7 := by
  decide +kernel

theorem configuration_33_lower_i8 : ConfigurationSlice 33 118 15 8 := by
  decide +kernel

theorem configuration_33_lower_i9 : ConfigurationSlice 33 118 15 9 := by
  decide +kernel

theorem configuration_33_lower_i10 : ConfigurationSlice 33 118 15 10 := by
  decide +kernel

theorem configuration_33_lower_i11 : ConfigurationSlice 33 118 15 11 := by
  decide +kernel

theorem configuration_33_lower_i12 : ConfigurationSlice 33 118 15 12 := by
  decide +kernel

theorem configuration_33_lower_i13 : ConfigurationSlice 33 118 15 13 := by
  decide +kernel

theorem configuration_33_lower_i14 : ConfigurationSlice 33 118 15 14 := by
  decide +kernel

theorem configuration_33_lower_i15 : ConfigurationSlice 33 118 15 15 := by
  decide +kernel

theorem configuration_33_lower_i16 : ConfigurationSlice 33 118 15 16 := by
  decide +kernel

theorem configuration_33_lower_i17 : ConfigurationSlice 33 118 15 17 := by
  decide +kernel

theorem configuration_33_lower_i18 : ConfigurationSlice 33 118 15 18 := by
  decide +kernel

theorem configuration_33_lower_i19 : ConfigurationSlice 33 118 15 19 := by
  decide +kernel

theorem configuration_33_lower_i20 : ConfigurationSlice 33 118 15 20 := by
  decide +kernel

theorem configuration_33_lower_i21 : ConfigurationSlice 33 118 15 21 := by
  decide +kernel

theorem configuration_33_lower_i22 : ConfigurationSlice 33 118 15 22 := by
  decide +kernel

theorem configuration_33_lower_i23 : ConfigurationSlice 33 118 15 23 := by
  decide +kernel

theorem configuration_33_lower_i24 : ConfigurationSlice 33 118 15 24 := by
  decide +kernel

theorem configuration_33_upper_i0 : ConfigurationSlice 33 118 16 0 := by
  decide +kernel

theorem configuration_33_upper_i1 : ConfigurationSlice 33 118 16 1 := by
  decide +kernel

theorem configuration_33_upper_i2 : ConfigurationSlice 33 118 16 2 := by
  decide +kernel

theorem configuration_33_upper_i3 : ConfigurationSlice 33 118 16 3 := by
  decide +kernel

theorem configuration_33_upper_i4 : ConfigurationSlice 33 118 16 4 := by
  decide +kernel

theorem configuration_33_upper_i5 : ConfigurationSlice 33 118 16 5 := by
  decide +kernel

theorem configuration_33_upper_i6 : ConfigurationSlice 33 118 16 6 := by
  decide +kernel

theorem configuration_33_upper_i7 : ConfigurationSlice 33 118 16 7 := by
  decide +kernel

theorem configuration_33_upper_i8 : ConfigurationSlice 33 118 16 8 := by
  decide +kernel

theorem configuration_33_upper_i9 : ConfigurationSlice 33 118 16 9 := by
  decide +kernel

theorem configuration_33_upper_i10 : ConfigurationSlice 33 118 16 10 := by
  decide +kernel

theorem configuration_33_upper_i11 : ConfigurationSlice 33 118 16 11 := by
  decide +kernel

theorem configuration_33_upper_i12 : ConfigurationSlice 33 118 16 12 := by
  decide +kernel

theorem configuration_33_upper_i13 : ConfigurationSlice 33 118 16 13 := by
  decide +kernel

theorem configuration_33_upper_i14 : ConfigurationSlice 33 118 16 14 := by
  decide +kernel

theorem configuration_33_upper_i15 : ConfigurationSlice 33 118 16 15 := by
  decide +kernel

theorem configuration_33_upper_i16 : ConfigurationSlice 33 118 16 16 := by
  decide +kernel

theorem configuration_33_upper_i17 : ConfigurationSlice 33 118 16 17 := by
  decide +kernel

theorem configuration_33_upper_i18 : ConfigurationSlice 33 118 16 18 := by
  decide +kernel

theorem configuration_33_upper_i19 : ConfigurationSlice 33 118 16 19 := by
  decide +kernel

theorem configuration_33_upper_i20 : ConfigurationSlice 33 118 16 20 := by
  decide +kernel

theorem configuration_33_upper_i21 : ConfigurationSlice 33 118 16 21 := by
  decide +kernel

theorem configuration_33_upper_i22 : ConfigurationSlice 33 118 16 22 := by
  decide +kernel

theorem configuration_33_upper_i23 : ConfigurationSlice 33 118 16 23 := by
  decide +kernel

theorem configuration_33_upper_i24 : ConfigurationSlice 33 118 16 24 := by
  decide +kernel

theorem configuration_33_upper_i25 : ConfigurationSlice 33 118 16 25 := by
  decide +kernel

theorem configuration_33_upper_i26 : ConfigurationSlice 33 118 16 26 := by
  decide +kernel

theorem configuration_34_lower_i0 : ConfigurationSlice 34 124 16 0 := by
  decide +kernel

theorem configuration_34_lower_i1 : ConfigurationSlice 34 124 16 1 := by
  decide +kernel

theorem configuration_34_lower_i2 : ConfigurationSlice 34 124 16 2 := by
  decide +kernel

theorem configuration_34_lower_i3 : ConfigurationSlice 34 124 16 3 := by
  decide +kernel

theorem configuration_34_lower_i4 : ConfigurationSlice 34 124 16 4 := by
  decide +kernel

theorem configuration_34_lower_i5 : ConfigurationSlice 34 124 16 5 := by
  decide +kernel

theorem configuration_34_lower_i6 : ConfigurationSlice 34 124 16 6 := by
  decide +kernel

theorem configuration_34_lower_i7 : ConfigurationSlice 34 124 16 7 := by
  decide +kernel

theorem configuration_34_lower_i8 : ConfigurationSlice 34 124 16 8 := by
  decide +kernel

theorem configuration_34_lower_i9 : ConfigurationSlice 34 124 16 9 := by
  decide +kernel

theorem configuration_34_lower_i10 : ConfigurationSlice 34 124 16 10 := by
  decide +kernel

theorem configuration_34_lower_i11 : ConfigurationSlice 34 124 16 11 := by
  decide +kernel

theorem configuration_34_lower_i12 : ConfigurationSlice 34 124 16 12 := by
  decide +kernel

theorem configuration_34_lower_i13 : ConfigurationSlice 34 124 16 13 := by
  decide +kernel

theorem configuration_34_lower_i14 : ConfigurationSlice 34 124 16 14 := by
  decide +kernel

theorem configuration_34_lower_i15 : ConfigurationSlice 34 124 16 15 := by
  decide +kernel

theorem configuration_34_lower_i16 : ConfigurationSlice 34 124 16 16 := by
  decide +kernel

theorem configuration_34_lower_i17 : ConfigurationSlice 34 124 16 17 := by
  decide +kernel

theorem configuration_34_lower_i18 : ConfigurationSlice 34 124 16 18 := by
  decide +kernel

theorem configuration_34_lower_i19 : ConfigurationSlice 34 124 16 19 := by
  decide +kernel

theorem configuration_34_lower_i20 : ConfigurationSlice 34 124 16 20 := by
  decide +kernel

theorem configuration_34_lower_i21 : ConfigurationSlice 34 124 16 21 := by
  decide +kernel

theorem configuration_34_lower_i22 : ConfigurationSlice 34 124 16 22 := by
  decide +kernel

theorem configuration_34_lower_i23 : ConfigurationSlice 34 124 16 23 := by
  decide +kernel

theorem configuration_34_lower_i24 : ConfigurationSlice 34 124 16 24 := by
  decide +kernel

theorem configuration_34_lower_i25 : ConfigurationSlice 34 124 16 25 := by
  decide +kernel

theorem configuration_34_lower_i26 : ConfigurationSlice 34 124 16 26 := by
  decide +kernel

theorem configuration_34_upper_i0 : ConfigurationSlice 34 124 17 0 := by
  decide +kernel

theorem configuration_34_upper_i1 : ConfigurationSlice 34 124 17 1 := by
  decide +kernel

theorem configuration_34_upper_i2 : ConfigurationSlice 34 124 17 2 := by
  decide +kernel

theorem configuration_34_upper_i3 : ConfigurationSlice 34 124 17 3 := by
  decide +kernel

theorem configuration_34_upper_i4 : ConfigurationSlice 34 124 17 4 := by
  decide +kernel

theorem configuration_34_upper_i5 : ConfigurationSlice 34 124 17 5 := by
  decide +kernel

theorem configuration_34_upper_i6 : ConfigurationSlice 34 124 17 6 := by
  decide +kernel

theorem configuration_34_upper_i7 : ConfigurationSlice 34 124 17 7 := by
  decide +kernel

theorem configuration_34_upper_i8 : ConfigurationSlice 34 124 17 8 := by
  decide +kernel

theorem configuration_34_upper_i9 : ConfigurationSlice 34 124 17 9 := by
  decide +kernel

theorem configuration_34_upper_i10 : ConfigurationSlice 34 124 17 10 := by
  decide +kernel

theorem configuration_34_upper_i11 : ConfigurationSlice 34 124 17 11 := by
  decide +kernel

theorem configuration_34_upper_i12 : ConfigurationSlice 34 124 17 12 := by
  decide +kernel

theorem configuration_34_upper_i13 : ConfigurationSlice 34 124 17 13 := by
  decide +kernel

theorem configuration_34_upper_i14 : ConfigurationSlice 34 124 17 14 := by
  decide +kernel

theorem configuration_34_upper_i15 : ConfigurationSlice 34 124 17 15 := by
  decide +kernel

theorem configuration_34_upper_i16 : ConfigurationSlice 34 124 17 16 := by
  decide +kernel

theorem configuration_34_upper_i17 : ConfigurationSlice 34 124 17 17 := by
  decide +kernel

theorem configuration_34_upper_i18 : ConfigurationSlice 34 124 17 18 := by
  decide +kernel

theorem configuration_34_upper_i19 : ConfigurationSlice 34 124 17 19 := by
  decide +kernel

theorem configuration_34_upper_i20 : ConfigurationSlice 34 124 17 20 := by
  decide +kernel

theorem configuration_34_upper_i21 : ConfigurationSlice 34 124 17 21 := by
  decide +kernel

theorem configuration_34_upper_i22 : ConfigurationSlice 34 124 17 22 := by
  decide +kernel

theorem configuration_34_upper_i23 : ConfigurationSlice 34 124 17 23 := by
  decide +kernel

theorem configuration_34_upper_i24 : ConfigurationSlice 34 124 17 24 := by
  decide +kernel

theorem configuration_34_upper_i25 : ConfigurationSlice 34 124 17 25 := by
  decide +kernel

theorem configuration_34_upper_i26 : ConfigurationSlice 34 124 17 26 := by
  decide +kernel

theorem configuration_34_upper_i27 : ConfigurationSlice 34 124 17 27 := by
  decide +kernel

theorem configuration_34_upper_i28 : ConfigurationSlice 34 124 17 28 := by
  decide +kernel

theorem configuration_35_lower_i0 : ConfigurationSlice 35 131 17 0 := by
  decide +kernel

theorem configuration_35_lower_i1 : ConfigurationSlice 35 131 17 1 := by
  decide +kernel

theorem configuration_35_lower_i2 : ConfigurationSlice 35 131 17 2 := by
  decide +kernel

theorem configuration_35_lower_i3 : ConfigurationSlice 35 131 17 3 := by
  decide +kernel

theorem configuration_35_lower_i4 : ConfigurationSlice 35 131 17 4 := by
  decide +kernel

theorem configuration_35_lower_i5 : ConfigurationSlice 35 131 17 5 := by
  decide +kernel

theorem configuration_35_lower_i6 : ConfigurationSlice 35 131 17 6 := by
  decide +kernel

theorem configuration_35_lower_i7 : ConfigurationSlice 35 131 17 7 := by
  decide +kernel

theorem configuration_35_lower_i8 : ConfigurationSlice 35 131 17 8 := by
  decide +kernel

theorem configuration_35_lower_i9 : ConfigurationSlice 35 131 17 9 := by
  decide +kernel

theorem configuration_35_lower_i10 : ConfigurationSlice 35 131 17 10 := by
  decide +kernel

theorem configuration_35_lower_i11 : ConfigurationSlice 35 131 17 11 := by
  decide +kernel

theorem configuration_35_lower_i12 : ConfigurationSlice 35 131 17 12 := by
  decide +kernel

theorem configuration_35_lower_i13 : ConfigurationSlice 35 131 17 13 := by
  decide +kernel

theorem configuration_35_lower_i14 : ConfigurationSlice 35 131 17 14 := by
  decide +kernel

theorem configuration_35_lower_i15 : ConfigurationSlice 35 131 17 15 := by
  decide +kernel

theorem configuration_35_lower_i16 : ConfigurationSlice 35 131 17 16 := by
  decide +kernel

theorem configuration_35_lower_i17 : ConfigurationSlice 35 131 17 17 := by
  decide +kernel

theorem configuration_35_lower_i18 : ConfigurationSlice 35 131 17 18 := by
  decide +kernel

theorem configuration_35_lower_i19 : ConfigurationSlice 35 131 17 19 := by
  decide +kernel

theorem configuration_35_lower_i20 : ConfigurationSlice 35 131 17 20 := by
  decide +kernel

theorem configuration_35_lower_i21 : ConfigurationSlice 35 131 17 21 := by
  decide +kernel

theorem configuration_35_lower_i22 : ConfigurationSlice 35 131 17 22 := by
  decide +kernel

theorem configuration_35_lower_i23 : ConfigurationSlice 35 131 17 23 := by
  decide +kernel

theorem configuration_35_lower_i24 : ConfigurationSlice 35 131 17 24 := by
  decide +kernel

theorem configuration_35_lower_i25 : ConfigurationSlice 35 131 17 25 := by
  decide +kernel

theorem configuration_35_lower_i26 : ConfigurationSlice 35 131 17 26 := by
  decide +kernel

theorem configuration_35_lower_i27 : ConfigurationSlice 35 131 17 27 := by
  decide +kernel

theorem configuration_35_lower_i28 : ConfigurationSlice 35 131 17 28 := by
  decide +kernel

theorem configuration_35_upper_i0 : ConfigurationSlice 35 131 18 0 := by
  decide +kernel

theorem configuration_35_upper_i1 : ConfigurationSlice 35 131 18 1 := by
  decide +kernel

theorem configuration_35_upper_i2 : ConfigurationSlice 35 131 18 2 := by
  decide +kernel

theorem configuration_35_upper_i3 : ConfigurationSlice 35 131 18 3 := by
  decide +kernel

theorem configuration_35_upper_i4 : ConfigurationSlice 35 131 18 4 := by
  decide +kernel

theorem configuration_35_upper_i5 : ConfigurationSlice 35 131 18 5 := by
  decide +kernel

theorem configuration_35_upper_i6 : ConfigurationSlice 35 131 18 6 := by
  decide +kernel

theorem configuration_35_upper_i7 : ConfigurationSlice 35 131 18 7 := by
  decide +kernel

theorem configuration_35_upper_i8 : ConfigurationSlice 35 131 18 8 := by
  decide +kernel

theorem configuration_35_upper_i9 : ConfigurationSlice 35 131 18 9 := by
  decide +kernel

theorem configuration_35_upper_i10 : ConfigurationSlice 35 131 18 10 := by
  decide +kernel

theorem configuration_35_upper_i11 : ConfigurationSlice 35 131 18 11 := by
  decide +kernel

theorem configuration_35_upper_i12 : ConfigurationSlice 35 131 18 12 := by
  decide +kernel

theorem configuration_35_upper_i13 : ConfigurationSlice 35 131 18 13 := by
  decide +kernel

theorem configuration_35_upper_i14 : ConfigurationSlice 35 131 18 14 := by
  decide +kernel

theorem configuration_35_upper_i15 : ConfigurationSlice 35 131 18 15 := by
  decide +kernel

theorem configuration_35_upper_i16 : ConfigurationSlice 35 131 18 16 := by
  decide +kernel

theorem configuration_35_upper_i17 : ConfigurationSlice 35 131 18 17 := by
  decide +kernel

theorem configuration_35_upper_i18 : ConfigurationSlice 35 131 18 18 := by
  decide +kernel

theorem configuration_35_upper_i19 : ConfigurationSlice 35 131 18 19 := by
  decide +kernel

theorem configuration_35_upper_i20 : ConfigurationSlice 35 131 18 20 := by
  decide +kernel

theorem configuration_35_upper_i21 : ConfigurationSlice 35 131 18 21 := by
  decide +kernel

theorem configuration_35_upper_i22 : ConfigurationSlice 35 131 18 22 := by
  decide +kernel

theorem configuration_35_upper_i23 : ConfigurationSlice 35 131 18 23 := by
  decide +kernel

theorem configuration_35_upper_i24 : ConfigurationSlice 35 131 18 24 := by
  decide +kernel

theorem configuration_35_upper_i25 : ConfigurationSlice 35 131 18 25 := by
  decide +kernel

theorem configuration_35_upper_i26 : ConfigurationSlice 35 131 18 26 := by
  decide +kernel

theorem configuration_35_upper_i27 : ConfigurationSlice 35 131 18 27 := by
  decide +kernel

theorem configuration_35_upper_i28 : ConfigurationSlice 35 131 18 28 := by
  decide +kernel

theorem configuration_35_upper_i29 : ConfigurationSlice 35 131 18 29 := by
  decide +kernel

theorem configuration_35_upper_i30 : ConfigurationSlice 35 131 18 30 := by
  decide +kernel

theorem configuration_36_lower_i0 : ConfigurationSlice 36 138 17 0 := by
  decide +kernel

theorem configuration_36_lower_i1 : ConfigurationSlice 36 138 17 1 := by
  decide +kernel

theorem configuration_36_lower_i2 : ConfigurationSlice 36 138 17 2 := by
  decide +kernel

theorem configuration_36_lower_i3 : ConfigurationSlice 36 138 17 3 := by
  decide +kernel

theorem configuration_36_lower_i4 : ConfigurationSlice 36 138 17 4 := by
  decide +kernel

theorem configuration_36_lower_i5 : ConfigurationSlice 36 138 17 5 := by
  decide +kernel

theorem configuration_36_lower_i6 : ConfigurationSlice 36 138 17 6 := by
  decide +kernel

theorem configuration_36_lower_i7 : ConfigurationSlice 36 138 17 7 := by
  decide +kernel

theorem configuration_36_lower_i8 : ConfigurationSlice 36 138 17 8 := by
  decide +kernel

theorem configuration_36_lower_i9 : ConfigurationSlice 36 138 17 9 := by
  decide +kernel

theorem configuration_36_lower_i10 : ConfigurationSlice 36 138 17 10 := by
  decide +kernel

theorem configuration_36_lower_i11 : ConfigurationSlice 36 138 17 11 := by
  decide +kernel

theorem configuration_36_lower_i12 : ConfigurationSlice 36 138 17 12 := by
  decide +kernel

theorem configuration_36_lower_i13 : ConfigurationSlice 36 138 17 13 := by
  decide +kernel

theorem configuration_36_lower_i14 : ConfigurationSlice 36 138 17 14 := by
  decide +kernel

theorem configuration_36_lower_i15 : ConfigurationSlice 36 138 17 15 := by
  decide +kernel

theorem configuration_36_lower_i16 : ConfigurationSlice 36 138 17 16 := by
  decide +kernel

theorem configuration_36_lower_i17 : ConfigurationSlice 36 138 17 17 := by
  decide +kernel

theorem configuration_36_lower_i18 : ConfigurationSlice 36 138 17 18 := by
  decide +kernel

theorem configuration_36_lower_i19 : ConfigurationSlice 36 138 17 19 := by
  decide +kernel

theorem configuration_36_lower_i20 : ConfigurationSlice 36 138 17 20 := by
  decide +kernel

theorem configuration_36_lower_i21 : ConfigurationSlice 36 138 17 21 := by
  decide +kernel

theorem configuration_36_lower_i22 : ConfigurationSlice 36 138 17 22 := by
  decide +kernel

theorem configuration_36_lower_i23 : ConfigurationSlice 36 138 17 23 := by
  decide +kernel

theorem configuration_36_lower_i24 : ConfigurationSlice 36 138 17 24 := by
  decide +kernel

theorem configuration_36_lower_i25 : ConfigurationSlice 36 138 17 25 := by
  decide +kernel

theorem configuration_36_lower_i26 : ConfigurationSlice 36 138 17 26 := by
  decide +kernel

theorem configuration_36_lower_i27 : ConfigurationSlice 36 138 17 27 := by
  decide +kernel

theorem configuration_36_lower_i28 : ConfigurationSlice 36 138 17 28 := by
  decide +kernel

theorem configuration_36_upper_i0 : ConfigurationSlice 36 138 18 0 := by
  decide +kernel

theorem configuration_36_upper_i1 : ConfigurationSlice 36 138 18 1 := by
  decide +kernel

theorem configuration_36_upper_i2 : ConfigurationSlice 36 138 18 2 := by
  decide +kernel

theorem configuration_36_upper_i3 : ConfigurationSlice 36 138 18 3 := by
  decide +kernel

theorem configuration_36_upper_i4 : ConfigurationSlice 36 138 18 4 := by
  decide +kernel

theorem configuration_36_upper_i5 : ConfigurationSlice 36 138 18 5 := by
  decide +kernel

theorem configuration_36_upper_i6 : ConfigurationSlice 36 138 18 6 := by
  decide +kernel

theorem configuration_36_upper_i7 : ConfigurationSlice 36 138 18 7 := by
  decide +kernel

theorem configuration_36_upper_i8 : ConfigurationSlice 36 138 18 8 := by
  decide +kernel

theorem configuration_36_upper_i9 : ConfigurationSlice 36 138 18 9 := by
  decide +kernel

theorem configuration_36_upper_i10 : ConfigurationSlice 36 138 18 10 := by
  decide +kernel

theorem configuration_36_upper_i11 : ConfigurationSlice 36 138 18 11 := by
  decide +kernel

theorem configuration_36_upper_i12 : ConfigurationSlice 36 138 18 12 := by
  decide +kernel

theorem configuration_36_upper_i13 : ConfigurationSlice 36 138 18 13 := by
  decide +kernel

theorem configuration_36_upper_i14 : ConfigurationSlice 36 138 18 14 := by
  decide +kernel

theorem configuration_36_upper_i15 : ConfigurationSlice 36 138 18 15 := by
  decide +kernel

theorem configuration_36_upper_i16 : ConfigurationSlice 36 138 18 16 := by
  decide +kernel

theorem configuration_36_upper_i17 : ConfigurationSlice 36 138 18 17 := by
  decide +kernel

theorem configuration_36_upper_i18 : ConfigurationSlice 36 138 18 18 := by
  decide +kernel

theorem configuration_36_upper_i19 : ConfigurationSlice 36 138 18 19 := by
  decide +kernel

theorem configuration_36_upper_i20 : ConfigurationSlice 36 138 18 20 := by
  decide +kernel

theorem configuration_36_upper_i21 : ConfigurationSlice 36 138 18 21 := by
  decide +kernel

theorem configuration_36_upper_i22 : ConfigurationSlice 36 138 18 22 := by
  decide +kernel

theorem configuration_36_upper_i23 : ConfigurationSlice 36 138 18 23 := by
  decide +kernel

theorem configuration_36_upper_i24 : ConfigurationSlice 36 138 18 24 := by
  decide +kernel

theorem configuration_36_upper_i25 : ConfigurationSlice 36 138 18 25 := by
  decide +kernel

theorem configuration_36_upper_i26 : ConfigurationSlice 36 138 18 26 := by
  decide +kernel

theorem configuration_36_upper_i27 : ConfigurationSlice 36 138 18 27 := by
  decide +kernel

theorem configuration_36_upper_i28 : ConfigurationSlice 36 138 18 28 := by
  decide +kernel

theorem configuration_36_upper_i29 : ConfigurationSlice 36 138 18 29 := by
  decide +kernel

theorem configuration_36_upper_i30 : ConfigurationSlice 36 138 18 30 := by
  decide +kernel

theorem configuration_37_lower_i0 : ConfigurationSlice 37 145 18 0 := by
  decide +kernel

theorem configuration_37_lower_i1 : ConfigurationSlice 37 145 18 1 := by
  decide +kernel

theorem configuration_37_lower_i2 : ConfigurationSlice 37 145 18 2 := by
  decide +kernel

theorem configuration_37_lower_i3 : ConfigurationSlice 37 145 18 3 := by
  decide +kernel

theorem configuration_37_lower_i4 : ConfigurationSlice 37 145 18 4 := by
  decide +kernel

theorem configuration_37_lower_i5 : ConfigurationSlice 37 145 18 5 := by
  decide +kernel

theorem configuration_37_lower_i6 : ConfigurationSlice 37 145 18 6 := by
  decide +kernel

theorem configuration_37_lower_i7 : ConfigurationSlice 37 145 18 7 := by
  decide +kernel

theorem configuration_37_lower_i8 : ConfigurationSlice 37 145 18 8 := by
  decide +kernel

theorem configuration_37_lower_i9 : ConfigurationSlice 37 145 18 9 := by
  decide +kernel

theorem configuration_37_lower_i10 : ConfigurationSlice 37 145 18 10 := by
  decide +kernel

theorem configuration_37_lower_i11 : ConfigurationSlice 37 145 18 11 := by
  decide +kernel

theorem configuration_37_lower_i12 : ConfigurationSlice 37 145 18 12 := by
  decide +kernel

theorem configuration_37_lower_i13 : ConfigurationSlice 37 145 18 13 := by
  decide +kernel

theorem configuration_37_lower_i14 : ConfigurationSlice 37 145 18 14 := by
  decide +kernel

theorem configuration_37_lower_i15 : ConfigurationSlice 37 145 18 15 := by
  decide +kernel

theorem configuration_37_lower_i16 : ConfigurationSlice 37 145 18 16 := by
  decide +kernel

theorem configuration_37_lower_i17 : ConfigurationSlice 37 145 18 17 := by
  decide +kernel

theorem configuration_37_lower_i18 : ConfigurationSlice 37 145 18 18 := by
  decide +kernel

theorem configuration_37_lower_i19 : ConfigurationSlice 37 145 18 19 := by
  decide +kernel

theorem configuration_37_lower_i20 : ConfigurationSlice 37 145 18 20 := by
  decide +kernel

theorem configuration_37_lower_i21 : ConfigurationSlice 37 145 18 21 := by
  decide +kernel

theorem configuration_37_lower_i22 : ConfigurationSlice 37 145 18 22 := by
  decide +kernel

theorem configuration_37_lower_i23 : ConfigurationSlice 37 145 18 23 := by
  decide +kernel

theorem configuration_37_lower_i24 : ConfigurationSlice 37 145 18 24 := by
  decide +kernel

theorem configuration_37_lower_i25 : ConfigurationSlice 37 145 18 25 := by
  decide +kernel

theorem configuration_37_lower_i26 : ConfigurationSlice 37 145 18 26 := by
  decide +kernel

theorem configuration_37_lower_i27 : ConfigurationSlice 37 145 18 27 := by
  decide +kernel

theorem configuration_37_lower_i28 : ConfigurationSlice 37 145 18 28 := by
  decide +kernel

theorem configuration_37_lower_i29 : ConfigurationSlice 37 145 18 29 := by
  decide +kernel

theorem configuration_37_lower_i30 : ConfigurationSlice 37 145 18 30 := by
  decide +kernel

theorem configuration_37_upper_i0 : ConfigurationSlice 37 145 19 0 := by
  decide +kernel

theorem configuration_37_upper_i1 : ConfigurationSlice 37 145 19 1 := by
  decide +kernel

theorem configuration_37_upper_i2 : ConfigurationSlice 37 145 19 2 := by
  decide +kernel

theorem configuration_37_upper_i3 : ConfigurationSlice 37 145 19 3 := by
  decide +kernel

theorem configuration_37_upper_i4 : ConfigurationSlice 37 145 19 4 := by
  decide +kernel

theorem configuration_37_upper_i5 : ConfigurationSlice 37 145 19 5 := by
  decide +kernel

theorem configuration_37_upper_i6 : ConfigurationSlice 37 145 19 6 := by
  decide +kernel

theorem configuration_37_upper_i7 : ConfigurationSlice 37 145 19 7 := by
  decide +kernel

theorem configuration_37_upper_i8 : ConfigurationSlice 37 145 19 8 := by
  decide +kernel

theorem configuration_37_upper_i9 : ConfigurationSlice 37 145 19 9 := by
  decide +kernel

theorem configuration_37_upper_i10 : ConfigurationSlice 37 145 19 10 := by
  decide +kernel

theorem configuration_37_upper_i11 : ConfigurationSlice 37 145 19 11 := by
  decide +kernel

theorem configuration_37_upper_i12 : ConfigurationSlice 37 145 19 12 := by
  decide +kernel

theorem configuration_37_upper_i13 : ConfigurationSlice 37 145 19 13 := by
  decide +kernel

theorem configuration_37_upper_i14 : ConfigurationSlice 37 145 19 14 := by
  decide +kernel

theorem configuration_37_upper_i15 : ConfigurationSlice 37 145 19 15 := by
  decide +kernel

theorem configuration_37_upper_i16 : ConfigurationSlice 37 145 19 16 := by
  decide +kernel

theorem configuration_37_upper_i17 : ConfigurationSlice 37 145 19 17 := by
  decide +kernel

theorem configuration_37_upper_i18 : ConfigurationSlice 37 145 19 18 := by
  decide +kernel

theorem configuration_37_upper_i19 : ConfigurationSlice 37 145 19 19 := by
  decide +kernel

theorem configuration_37_upper_i20 : ConfigurationSlice 37 145 19 20 := by
  decide +kernel

theorem configuration_37_upper_i21 : ConfigurationSlice 37 145 19 21 := by
  decide +kernel

theorem configuration_37_upper_i22 : ConfigurationSlice 37 145 19 22 := by
  decide +kernel

theorem configuration_37_upper_i23 : ConfigurationSlice 37 145 19 23 := by
  decide +kernel

theorem configuration_37_upper_i24 : ConfigurationSlice 37 145 19 24 := by
  decide +kernel

theorem configuration_37_upper_i25 : ConfigurationSlice 37 145 19 25 := by
  decide +kernel

theorem configuration_37_upper_i26 : ConfigurationSlice 37 145 19 26 := by
  decide +kernel

theorem configuration_37_upper_i27 : ConfigurationSlice 37 145 19 27 := by
  decide +kernel

theorem configuration_37_upper_i28 : ConfigurationSlice 37 145 19 28 := by
  decide +kernel

theorem configuration_37_upper_i29 : ConfigurationSlice 37 145 19 29 := by
  decide +kernel

theorem configuration_37_upper_i30 : ConfigurationSlice 37 145 19 30 := by
  decide +kernel

theorem configuration_37_upper_i31 : ConfigurationSlice 37 145 19 31 := by
  decide +kernel

theorem configuration_37_upper_i32 : ConfigurationSlice 37 145 19 32 := by
  decide +kernel

theorem configuration_38_lower_i0 : ConfigurationSlice 38 153 18 0 := by
  decide +kernel

theorem configuration_38_lower_i1 : ConfigurationSlice 38 153 18 1 := by
  decide +kernel

theorem configuration_38_lower_i2 : ConfigurationSlice 38 153 18 2 := by
  decide +kernel

theorem configuration_38_lower_i3 : ConfigurationSlice 38 153 18 3 := by
  decide +kernel

theorem configuration_38_lower_i4 : ConfigurationSlice 38 153 18 4 := by
  decide +kernel

theorem configuration_38_lower_i5 : ConfigurationSlice 38 153 18 5 := by
  decide +kernel

theorem configuration_38_lower_i6 : ConfigurationSlice 38 153 18 6 := by
  decide +kernel

theorem configuration_38_lower_i7 : ConfigurationSlice 38 153 18 7 := by
  decide +kernel

theorem configuration_38_lower_i8 : ConfigurationSlice 38 153 18 8 := by
  decide +kernel

theorem configuration_38_lower_i9 : ConfigurationSlice 38 153 18 9 := by
  decide +kernel

theorem configuration_38_lower_i10 : ConfigurationSlice 38 153 18 10 := by
  decide +kernel

theorem configuration_38_lower_i11 : ConfigurationSlice 38 153 18 11 := by
  decide +kernel

theorem configuration_38_lower_i12 : ConfigurationSlice 38 153 18 12 := by
  decide +kernel

theorem configuration_38_lower_i13 : ConfigurationSlice 38 153 18 13 := by
  decide +kernel

theorem configuration_38_lower_i14 : ConfigurationSlice 38 153 18 14 := by
  decide +kernel

theorem configuration_38_lower_i15 : ConfigurationSlice 38 153 18 15 := by
  decide +kernel

theorem configuration_38_lower_i16 : ConfigurationSlice 38 153 18 16 := by
  decide +kernel

theorem configuration_38_lower_i17 : ConfigurationSlice 38 153 18 17 := by
  decide +kernel

theorem configuration_38_lower_i18 : ConfigurationSlice 38 153 18 18 := by
  decide +kernel

theorem configuration_38_lower_i19 : ConfigurationSlice 38 153 18 19 := by
  decide +kernel

theorem configuration_38_lower_i20 : ConfigurationSlice 38 153 18 20 := by
  decide +kernel

theorem configuration_38_lower_i21 : ConfigurationSlice 38 153 18 21 := by
  decide +kernel

theorem configuration_38_lower_i22 : ConfigurationSlice 38 153 18 22 := by
  decide +kernel

theorem configuration_38_lower_i23 : ConfigurationSlice 38 153 18 23 := by
  decide +kernel

theorem configuration_38_lower_i24 : ConfigurationSlice 38 153 18 24 := by
  decide +kernel

theorem configuration_38_lower_i25 : ConfigurationSlice 38 153 18 25 := by
  decide +kernel

theorem configuration_38_lower_i26 : ConfigurationSlice 38 153 18 26 := by
  decide +kernel

theorem configuration_38_lower_i27 : ConfigurationSlice 38 153 18 27 := by
  decide +kernel

theorem configuration_38_lower_i28 : ConfigurationSlice 38 153 18 28 := by
  decide +kernel

theorem configuration_38_lower_i29 : ConfigurationSlice 38 153 18 29 := by
  decide +kernel

theorem configuration_38_lower_i30 : ConfigurationSlice 38 153 18 30 := by
  decide +kernel

theorem configuration_38_upper_i0 : ConfigurationSlice 38 153 19 0 := by
  decide +kernel

theorem configuration_38_upper_i1 : ConfigurationSlice 38 153 19 1 := by
  decide +kernel

theorem configuration_38_upper_i2 : ConfigurationSlice 38 153 19 2 := by
  decide +kernel

theorem configuration_38_upper_i3 : ConfigurationSlice 38 153 19 3 := by
  decide +kernel

theorem configuration_38_upper_i4 : ConfigurationSlice 38 153 19 4 := by
  decide +kernel

theorem configuration_38_upper_i5 : ConfigurationSlice 38 153 19 5 := by
  decide +kernel

theorem configuration_38_upper_i6 : ConfigurationSlice 38 153 19 6 := by
  decide +kernel

theorem configuration_38_upper_i7 : ConfigurationSlice 38 153 19 7 := by
  decide +kernel

theorem configuration_38_upper_i8 : ConfigurationSlice 38 153 19 8 := by
  decide +kernel

theorem configuration_38_upper_i9 : ConfigurationSlice 38 153 19 9 := by
  decide +kernel

theorem configuration_38_upper_i10 : ConfigurationSlice 38 153 19 10 := by
  decide +kernel

theorem configuration_38_upper_i11 : ConfigurationSlice 38 153 19 11 := by
  decide +kernel

theorem configuration_38_upper_i12 : ConfigurationSlice 38 153 19 12 := by
  decide +kernel

theorem configuration_38_upper_i13 : ConfigurationSlice 38 153 19 13 := by
  decide +kernel

theorem configuration_38_upper_i14 : ConfigurationSlice 38 153 19 14 := by
  decide +kernel

theorem configuration_38_upper_i15 : ConfigurationSlice 38 153 19 15 := by
  decide +kernel

theorem configuration_38_upper_i16 : ConfigurationSlice 38 153 19 16 := by
  decide +kernel

theorem configuration_38_upper_i17 : ConfigurationSlice 38 153 19 17 := by
  decide +kernel

theorem configuration_38_upper_i18 : ConfigurationSlice 38 153 19 18 := by
  decide +kernel

theorem configuration_38_upper_i19 : ConfigurationSlice 38 153 19 19 := by
  decide +kernel

theorem configuration_38_upper_i20 : ConfigurationSlice 38 153 19 20 := by
  decide +kernel

theorem configuration_38_upper_i21 : ConfigurationSlice 38 153 19 21 := by
  decide +kernel

theorem configuration_38_upper_i22 : ConfigurationSlice 38 153 19 22 := by
  decide +kernel

theorem configuration_38_upper_i23 : ConfigurationSlice 38 153 19 23 := by
  decide +kernel

theorem configuration_38_upper_i24 : ConfigurationSlice 38 153 19 24 := by
  decide +kernel

theorem configuration_38_upper_i25 : ConfigurationSlice 38 153 19 25 := by
  decide +kernel

theorem configuration_38_upper_i26 : ConfigurationSlice 38 153 19 26 := by
  decide +kernel

theorem configuration_38_upper_i27 : ConfigurationSlice 38 153 19 27 := by
  decide +kernel

theorem configuration_38_upper_i28 : ConfigurationSlice 38 153 19 28 := by
  decide +kernel

theorem configuration_38_upper_i29 : ConfigurationSlice 38 153 19 29 := by
  decide +kernel

theorem configuration_38_upper_i30 : ConfigurationSlice 38 153 19 30 := by
  decide +kernel

theorem configuration_38_upper_i31 : ConfigurationSlice 38 153 19 31 := by
  decide +kernel

theorem configuration_38_upper_i32 : ConfigurationSlice 38 153 19 32 := by
  decide +kernel

theorem configuration_39_lower_i0 : ConfigurationSlice 39 160 19 0 := by
  decide +kernel

theorem configuration_39_lower_i1 : ConfigurationSlice 39 160 19 1 := by
  decide +kernel

theorem configuration_39_lower_i2 : ConfigurationSlice 39 160 19 2 := by
  decide +kernel

theorem configuration_39_lower_i3 : ConfigurationSlice 39 160 19 3 := by
  decide +kernel

theorem configuration_39_lower_i4 : ConfigurationSlice 39 160 19 4 := by
  decide +kernel

theorem configuration_39_lower_i5 : ConfigurationSlice 39 160 19 5 := by
  decide +kernel

theorem configuration_39_lower_i6 : ConfigurationSlice 39 160 19 6 := by
  decide +kernel

theorem configuration_39_lower_i7 : ConfigurationSlice 39 160 19 7 := by
  decide +kernel

theorem configuration_39_lower_i8 : ConfigurationSlice 39 160 19 8 := by
  decide +kernel

theorem configuration_39_lower_i9 : ConfigurationSlice 39 160 19 9 := by
  decide +kernel

theorem configuration_39_lower_i10 : ConfigurationSlice 39 160 19 10 := by
  decide +kernel

theorem configuration_39_lower_i11 : ConfigurationSlice 39 160 19 11 := by
  decide +kernel

theorem configuration_39_lower_i12 : ConfigurationSlice 39 160 19 12 := by
  decide +kernel

theorem configuration_39_lower_i13 : ConfigurationSlice 39 160 19 13 := by
  decide +kernel

theorem configuration_39_lower_i14 : ConfigurationSlice 39 160 19 14 := by
  decide +kernel

theorem configuration_39_lower_i15 : ConfigurationSlice 39 160 19 15 := by
  decide +kernel

theorem configuration_39_lower_i16 : ConfigurationSlice 39 160 19 16 := by
  decide +kernel

theorem configuration_39_lower_i17 : ConfigurationSlice 39 160 19 17 := by
  decide +kernel

theorem configuration_39_lower_i18 : ConfigurationSlice 39 160 19 18 := by
  decide +kernel

theorem configuration_39_lower_i19 : ConfigurationSlice 39 160 19 19 := by
  decide +kernel

theorem configuration_39_lower_i20 : ConfigurationSlice 39 160 19 20 := by
  decide +kernel

theorem configuration_39_lower_i21 : ConfigurationSlice 39 160 19 21 := by
  decide +kernel

theorem configuration_39_lower_i22 : ConfigurationSlice 39 160 19 22 := by
  decide +kernel

theorem configuration_39_lower_i23 : ConfigurationSlice 39 160 19 23 := by
  decide +kernel

theorem configuration_39_lower_i24 : ConfigurationSlice 39 160 19 24 := by
  decide +kernel

theorem configuration_39_lower_i25 : ConfigurationSlice 39 160 19 25 := by
  decide +kernel

theorem configuration_39_lower_i26 : ConfigurationSlice 39 160 19 26 := by
  decide +kernel

theorem configuration_39_lower_i27 : ConfigurationSlice 39 160 19 27 := by
  decide +kernel

theorem configuration_39_lower_i28 : ConfigurationSlice 39 160 19 28 := by
  decide +kernel

theorem configuration_39_lower_i29 : ConfigurationSlice 39 160 19 29 := by
  decide +kernel

theorem configuration_39_lower_i30 : ConfigurationSlice 39 160 19 30 := by
  decide +kernel

theorem configuration_39_lower_i31 : ConfigurationSlice 39 160 19 31 := by
  decide +kernel

theorem configuration_39_lower_i32 : ConfigurationSlice 39 160 19 32 := by
  decide +kernel

theorem configuration_39_upper_i0 : ConfigurationSlice 39 160 20 0 := by
  decide +kernel

theorem configuration_39_upper_i1 : ConfigurationSlice 39 160 20 1 := by
  decide +kernel

theorem configuration_39_upper_i2 : ConfigurationSlice 39 160 20 2 := by
  decide +kernel

theorem configuration_39_upper_i3 : ConfigurationSlice 39 160 20 3 := by
  decide +kernel

theorem configuration_39_upper_i4 : ConfigurationSlice 39 160 20 4 := by
  decide +kernel

theorem configuration_39_upper_i5 : ConfigurationSlice 39 160 20 5 := by
  decide +kernel

theorem configuration_39_upper_i6 : ConfigurationSlice 39 160 20 6 := by
  decide +kernel

theorem configuration_39_upper_i7 : ConfigurationSlice 39 160 20 7 := by
  decide +kernel

theorem configuration_39_upper_i8 : ConfigurationSlice 39 160 20 8 := by
  decide +kernel

theorem configuration_39_upper_i9 : ConfigurationSlice 39 160 20 9 := by
  decide +kernel

theorem configuration_39_upper_i10 : ConfigurationSlice 39 160 20 10 := by
  decide +kernel

theorem configuration_39_upper_i11 : ConfigurationSlice 39 160 20 11 := by
  decide +kernel

theorem configuration_39_upper_i12 : ConfigurationSlice 39 160 20 12 := by
  decide +kernel

theorem configuration_39_upper_i13 : ConfigurationSlice 39 160 20 13 := by
  decide +kernel

theorem configuration_39_upper_i14 : ConfigurationSlice 39 160 20 14 := by
  decide +kernel

theorem configuration_39_upper_i15 : ConfigurationSlice 39 160 20 15 := by
  decide +kernel

theorem configuration_39_upper_i16 : ConfigurationSlice 39 160 20 16 := by
  decide +kernel

theorem configuration_39_upper_i17 : ConfigurationSlice 39 160 20 17 := by
  decide +kernel

theorem configuration_39_upper_i18 : ConfigurationSlice 39 160 20 18 := by
  decide +kernel

theorem configuration_39_upper_i19 : ConfigurationSlice 39 160 20 19 := by
  decide +kernel

theorem configuration_39_upper_i20 : ConfigurationSlice 39 160 20 20 := by
  decide +kernel

theorem configuration_39_upper_i21 : ConfigurationSlice 39 160 20 21 := by
  decide +kernel

theorem configuration_39_upper_i22 : ConfigurationSlice 39 160 20 22 := by
  decide +kernel

theorem configuration_39_upper_i23 : ConfigurationSlice 39 160 20 23 := by
  decide +kernel

theorem configuration_39_upper_i24 : ConfigurationSlice 39 160 20 24 := by
  decide +kernel

theorem configuration_39_upper_i25 : ConfigurationSlice 39 160 20 25 := by
  decide +kernel

theorem configuration_39_upper_i26 : ConfigurationSlice 39 160 20 26 := by
  decide +kernel

theorem configuration_39_upper_i27 : ConfigurationSlice 39 160 20 27 := by
  decide +kernel

theorem configuration_39_upper_i28 : ConfigurationSlice 39 160 20 28 := by
  decide +kernel

theorem configuration_39_upper_i29 : ConfigurationSlice 39 160 20 29 := by
  decide +kernel

theorem configuration_39_upper_i30 : ConfigurationSlice 39 160 20 30 := by
  decide +kernel

theorem configuration_39_upper_i31 : ConfigurationSlice 39 160 20 31 := by
  decide +kernel

theorem configuration_39_upper_i32 : ConfigurationSlice 39 160 20 32 := by
  decide +kernel

theorem configuration_39_upper_i33 : ConfigurationSlice 39 160 20 33 := by
  decide +kernel

theorem configuration_39_upper_i34 : ConfigurationSlice 39 160 20 34 := by
  decide +kernel

theorem configuration_40_lower_i0 : ConfigurationSlice 40 168 19 0 := by
  decide +kernel

theorem configuration_40_lower_i1 : ConfigurationSlice 40 168 19 1 := by
  decide +kernel

theorem configuration_40_lower_i2 : ConfigurationSlice 40 168 19 2 := by
  decide +kernel

theorem configuration_40_lower_i3 : ConfigurationSlice 40 168 19 3 := by
  decide +kernel

theorem configuration_40_lower_i4 : ConfigurationSlice 40 168 19 4 := by
  decide +kernel

theorem configuration_40_lower_i5 : ConfigurationSlice 40 168 19 5 := by
  decide +kernel

theorem configuration_40_lower_i6 : ConfigurationSlice 40 168 19 6 := by
  decide +kernel

theorem configuration_40_lower_i7 : ConfigurationSlice 40 168 19 7 := by
  decide +kernel

theorem configuration_40_lower_i8 : ConfigurationSlice 40 168 19 8 := by
  decide +kernel

theorem configuration_40_lower_i9 : ConfigurationSlice 40 168 19 9 := by
  decide +kernel

theorem configuration_40_lower_i10 : ConfigurationSlice 40 168 19 10 := by
  decide +kernel

theorem configuration_40_lower_i11 : ConfigurationSlice 40 168 19 11 := by
  decide +kernel

theorem configuration_40_lower_i12 : ConfigurationSlice 40 168 19 12 := by
  decide +kernel

theorem configuration_40_lower_i13 : ConfigurationSlice 40 168 19 13 := by
  decide +kernel

theorem configuration_40_lower_i14 : ConfigurationSlice 40 168 19 14 := by
  decide +kernel

theorem configuration_40_lower_i15 : ConfigurationSlice 40 168 19 15 := by
  decide +kernel

theorem configuration_40_lower_i16 : ConfigurationSlice 40 168 19 16 := by
  decide +kernel

theorem configuration_40_lower_i17 : ConfigurationSlice 40 168 19 17 := by
  decide +kernel

theorem configuration_40_lower_i18 : ConfigurationSlice 40 168 19 18 := by
  decide +kernel

theorem configuration_40_lower_i19 : ConfigurationSlice 40 168 19 19 := by
  decide +kernel

theorem configuration_40_lower_i20 : ConfigurationSlice 40 168 19 20 := by
  decide +kernel

theorem configuration_40_lower_i21 : ConfigurationSlice 40 168 19 21 := by
  decide +kernel

theorem configuration_40_lower_i22 : ConfigurationSlice 40 168 19 22 := by
  decide +kernel

theorem configuration_40_lower_i23 : ConfigurationSlice 40 168 19 23 := by
  decide +kernel

theorem configuration_40_lower_i24 : ConfigurationSlice 40 168 19 24 := by
  decide +kernel

theorem configuration_40_lower_i25 : ConfigurationSlice 40 168 19 25 := by
  decide +kernel

theorem configuration_40_lower_i26 : ConfigurationSlice 40 168 19 26 := by
  decide +kernel

theorem configuration_40_lower_i27 : ConfigurationSlice 40 168 19 27 := by
  decide +kernel

theorem configuration_40_lower_i28 : ConfigurationSlice 40 168 19 28 := by
  decide +kernel

theorem configuration_40_lower_i29 : ConfigurationSlice 40 168 19 29 := by
  decide +kernel

theorem configuration_40_lower_i30 : ConfigurationSlice 40 168 19 30 := by
  decide +kernel

theorem configuration_40_lower_i31 : ConfigurationSlice 40 168 19 31 := by
  decide +kernel

theorem configuration_40_lower_i32 : ConfigurationSlice 40 168 19 32 := by
  decide +kernel

theorem configuration_40_upper_i0 : ConfigurationSlice 40 168 20 0 := by
  decide +kernel

theorem configuration_40_upper_i1 : ConfigurationSlice 40 168 20 1 := by
  decide +kernel

theorem configuration_40_upper_i2 : ConfigurationSlice 40 168 20 2 := by
  decide +kernel

theorem configuration_40_upper_i3 : ConfigurationSlice 40 168 20 3 := by
  decide +kernel

theorem configuration_40_upper_i4 : ConfigurationSlice 40 168 20 4 := by
  decide +kernel

theorem configuration_40_upper_i5 : ConfigurationSlice 40 168 20 5 := by
  decide +kernel

theorem configuration_40_upper_i6 : ConfigurationSlice 40 168 20 6 := by
  decide +kernel

theorem configuration_40_upper_i7 : ConfigurationSlice 40 168 20 7 := by
  decide +kernel

theorem configuration_40_upper_i8 : ConfigurationSlice 40 168 20 8 := by
  decide +kernel

theorem configuration_40_upper_i9 : ConfigurationSlice 40 168 20 9 := by
  decide +kernel

theorem configuration_40_upper_i10 : ConfigurationSlice 40 168 20 10 := by
  decide +kernel

theorem configuration_40_upper_i11 : ConfigurationSlice 40 168 20 11 := by
  decide +kernel

theorem configuration_40_upper_i12 : ConfigurationSlice 40 168 20 12 := by
  decide +kernel

theorem configuration_40_upper_i13 : ConfigurationSlice 40 168 20 13 := by
  decide +kernel

theorem configuration_40_upper_i14 : ConfigurationSlice 40 168 20 14 := by
  decide +kernel

theorem configuration_40_upper_i15 : ConfigurationSlice 40 168 20 15 := by
  decide +kernel

theorem configuration_40_upper_i16 : ConfigurationSlice 40 168 20 16 := by
  decide +kernel

theorem configuration_40_upper_i17 : ConfigurationSlice 40 168 20 17 := by
  decide +kernel

theorem configuration_40_upper_i18 : ConfigurationSlice 40 168 20 18 := by
  decide +kernel

theorem configuration_40_upper_i19 : ConfigurationSlice 40 168 20 19 := by
  decide +kernel

theorem configuration_40_upper_i20 : ConfigurationSlice 40 168 20 20 := by
  decide +kernel

theorem configuration_40_upper_i21 : ConfigurationSlice 40 168 20 21 := by
  decide +kernel

theorem configuration_40_upper_i22 : ConfigurationSlice 40 168 20 22 := by
  decide +kernel

theorem configuration_40_upper_i23 : ConfigurationSlice 40 168 20 23 := by
  decide +kernel

theorem configuration_40_upper_i24 : ConfigurationSlice 40 168 20 24 := by
  decide +kernel

theorem configuration_40_upper_i25 : ConfigurationSlice 40 168 20 25 := by
  decide +kernel

theorem configuration_40_upper_i26 : ConfigurationSlice 40 168 20 26 := by
  decide +kernel

theorem configuration_40_upper_i27 : ConfigurationSlice 40 168 20 27 := by
  decide +kernel

theorem configuration_40_upper_i28 : ConfigurationSlice 40 168 20 28 := by
  decide +kernel

theorem configuration_40_upper_i29 : ConfigurationSlice 40 168 20 29 := by
  decide +kernel

theorem configuration_40_upper_i30 : ConfigurationSlice 40 168 20 30 := by
  decide +kernel

theorem configuration_40_upper_i31 : ConfigurationSlice 40 168 20 31 := by
  decide +kernel

theorem configuration_40_upper_i32 : ConfigurationSlice 40 168 20 32 := by
  decide +kernel

theorem configuration_40_upper_i33 : ConfigurationSlice 40 168 20 33 := by
  decide +kernel

theorem configuration_40_upper_i34 : ConfigurationSlice 40 168 20 34 := by
  decide +kernel

end Slices

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_28_lower : ConfigurationValid 28 87 13 := by
  intro i
  fin_cases i
  · exact Slices.configuration_28_lower_i0
  · exact Slices.configuration_28_lower_i1
  · exact Slices.configuration_28_lower_i2
  · exact Slices.configuration_28_lower_i3
  · exact Slices.configuration_28_lower_i4
  · exact Slices.configuration_28_lower_i5
  · exact Slices.configuration_28_lower_i6
  · exact Slices.configuration_28_lower_i7
  · exact Slices.configuration_28_lower_i8
  · exact Slices.configuration_28_lower_i9
  · exact Slices.configuration_28_lower_i10
  · exact Slices.configuration_28_lower_i11
  · exact Slices.configuration_28_lower_i12
  · exact Slices.configuration_28_lower_i13
  · exact Slices.configuration_28_lower_i14
  · exact Slices.configuration_28_lower_i15
  · exact Slices.configuration_28_lower_i16
  · exact Slices.configuration_28_lower_i17
  · exact Slices.configuration_28_lower_i18
  · exact Slices.configuration_28_lower_i19
  · exact Slices.configuration_28_lower_i20

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_28_upper : ConfigurationValid 28 87 14 := by
  intro i
  fin_cases i
  · exact Slices.configuration_28_upper_i0
  · exact Slices.configuration_28_upper_i1
  · exact Slices.configuration_28_upper_i2
  · exact Slices.configuration_28_upper_i3
  · exact Slices.configuration_28_upper_i4
  · exact Slices.configuration_28_upper_i5
  · exact Slices.configuration_28_upper_i6
  · exact Slices.configuration_28_upper_i7
  · exact Slices.configuration_28_upper_i8
  · exact Slices.configuration_28_upper_i9
  · exact Slices.configuration_28_upper_i10
  · exact Slices.configuration_28_upper_i11
  · exact Slices.configuration_28_upper_i12
  · exact Slices.configuration_28_upper_i13
  · exact Slices.configuration_28_upper_i14
  · exact Slices.configuration_28_upper_i15
  · exact Slices.configuration_28_upper_i16
  · exact Slices.configuration_28_upper_i17
  · exact Slices.configuration_28_upper_i18
  · exact Slices.configuration_28_upper_i19
  · exact Slices.configuration_28_upper_i20
  · exact Slices.configuration_28_upper_i21
  · exact Slices.configuration_28_upper_i22

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_29_lower : ConfigurationValid 29 93 13 := by
  intro i
  fin_cases i
  · exact Slices.configuration_29_lower_i0
  · exact Slices.configuration_29_lower_i1
  · exact Slices.configuration_29_lower_i2
  · exact Slices.configuration_29_lower_i3
  · exact Slices.configuration_29_lower_i4
  · exact Slices.configuration_29_lower_i5
  · exact Slices.configuration_29_lower_i6
  · exact Slices.configuration_29_lower_i7
  · exact Slices.configuration_29_lower_i8
  · exact Slices.configuration_29_lower_i9
  · exact Slices.configuration_29_lower_i10
  · exact Slices.configuration_29_lower_i11
  · exact Slices.configuration_29_lower_i12
  · exact Slices.configuration_29_lower_i13
  · exact Slices.configuration_29_lower_i14
  · exact Slices.configuration_29_lower_i15
  · exact Slices.configuration_29_lower_i16
  · exact Slices.configuration_29_lower_i17
  · exact Slices.configuration_29_lower_i18
  · exact Slices.configuration_29_lower_i19
  · exact Slices.configuration_29_lower_i20

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_29_upper : ConfigurationValid 29 93 14 := by
  intro i
  fin_cases i
  · exact Slices.configuration_29_upper_i0
  · exact Slices.configuration_29_upper_i1
  · exact Slices.configuration_29_upper_i2
  · exact Slices.configuration_29_upper_i3
  · exact Slices.configuration_29_upper_i4
  · exact Slices.configuration_29_upper_i5
  · exact Slices.configuration_29_upper_i6
  · exact Slices.configuration_29_upper_i7
  · exact Slices.configuration_29_upper_i8
  · exact Slices.configuration_29_upper_i9
  · exact Slices.configuration_29_upper_i10
  · exact Slices.configuration_29_upper_i11
  · exact Slices.configuration_29_upper_i12
  · exact Slices.configuration_29_upper_i13
  · exact Slices.configuration_29_upper_i14
  · exact Slices.configuration_29_upper_i15
  · exact Slices.configuration_29_upper_i16
  · exact Slices.configuration_29_upper_i17
  · exact Slices.configuration_29_upper_i18
  · exact Slices.configuration_29_upper_i19
  · exact Slices.configuration_29_upper_i20
  · exact Slices.configuration_29_upper_i21
  · exact Slices.configuration_29_upper_i22

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_30_lower : ConfigurationValid 30 99 14 := by
  intro i
  fin_cases i
  · exact Slices.configuration_30_lower_i0
  · exact Slices.configuration_30_lower_i1
  · exact Slices.configuration_30_lower_i2
  · exact Slices.configuration_30_lower_i3
  · exact Slices.configuration_30_lower_i4
  · exact Slices.configuration_30_lower_i5
  · exact Slices.configuration_30_lower_i6
  · exact Slices.configuration_30_lower_i7
  · exact Slices.configuration_30_lower_i8
  · exact Slices.configuration_30_lower_i9
  · exact Slices.configuration_30_lower_i10
  · exact Slices.configuration_30_lower_i11
  · exact Slices.configuration_30_lower_i12
  · exact Slices.configuration_30_lower_i13
  · exact Slices.configuration_30_lower_i14
  · exact Slices.configuration_30_lower_i15
  · exact Slices.configuration_30_lower_i16
  · exact Slices.configuration_30_lower_i17
  · exact Slices.configuration_30_lower_i18
  · exact Slices.configuration_30_lower_i19
  · exact Slices.configuration_30_lower_i20
  · exact Slices.configuration_30_lower_i21
  · exact Slices.configuration_30_lower_i22

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_30_upper : ConfigurationValid 30 99 15 := by
  intro i
  fin_cases i
  · exact Slices.configuration_30_upper_i0
  · exact Slices.configuration_30_upper_i1
  · exact Slices.configuration_30_upper_i2
  · exact Slices.configuration_30_upper_i3
  · exact Slices.configuration_30_upper_i4
  · exact Slices.configuration_30_upper_i5
  · exact Slices.configuration_30_upper_i6
  · exact Slices.configuration_30_upper_i7
  · exact Slices.configuration_30_upper_i8
  · exact Slices.configuration_30_upper_i9
  · exact Slices.configuration_30_upper_i10
  · exact Slices.configuration_30_upper_i11
  · exact Slices.configuration_30_upper_i12
  · exact Slices.configuration_30_upper_i13
  · exact Slices.configuration_30_upper_i14
  · exact Slices.configuration_30_upper_i15
  · exact Slices.configuration_30_upper_i16
  · exact Slices.configuration_30_upper_i17
  · exact Slices.configuration_30_upper_i18
  · exact Slices.configuration_30_upper_i19
  · exact Slices.configuration_30_upper_i20
  · exact Slices.configuration_30_upper_i21
  · exact Slices.configuration_30_upper_i22
  · exact Slices.configuration_30_upper_i23
  · exact Slices.configuration_30_upper_i24

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_31_lower : ConfigurationValid 31 105 14 := by
  intro i
  fin_cases i
  · exact Slices.configuration_31_lower_i0
  · exact Slices.configuration_31_lower_i1
  · exact Slices.configuration_31_lower_i2
  · exact Slices.configuration_31_lower_i3
  · exact Slices.configuration_31_lower_i4
  · exact Slices.configuration_31_lower_i5
  · exact Slices.configuration_31_lower_i6
  · exact Slices.configuration_31_lower_i7
  · exact Slices.configuration_31_lower_i8
  · exact Slices.configuration_31_lower_i9
  · exact Slices.configuration_31_lower_i10
  · exact Slices.configuration_31_lower_i11
  · exact Slices.configuration_31_lower_i12
  · exact Slices.configuration_31_lower_i13
  · exact Slices.configuration_31_lower_i14
  · exact Slices.configuration_31_lower_i15
  · exact Slices.configuration_31_lower_i16
  · exact Slices.configuration_31_lower_i17
  · exact Slices.configuration_31_lower_i18
  · exact Slices.configuration_31_lower_i19
  · exact Slices.configuration_31_lower_i20
  · exact Slices.configuration_31_lower_i21
  · exact Slices.configuration_31_lower_i22

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_31_upper : ConfigurationValid 31 105 15 := by
  intro i
  fin_cases i
  · exact Slices.configuration_31_upper_i0
  · exact Slices.configuration_31_upper_i1
  · exact Slices.configuration_31_upper_i2
  · exact Slices.configuration_31_upper_i3
  · exact Slices.configuration_31_upper_i4
  · exact Slices.configuration_31_upper_i5
  · exact Slices.configuration_31_upper_i6
  · exact Slices.configuration_31_upper_i7
  · exact Slices.configuration_31_upper_i8
  · exact Slices.configuration_31_upper_i9
  · exact Slices.configuration_31_upper_i10
  · exact Slices.configuration_31_upper_i11
  · exact Slices.configuration_31_upper_i12
  · exact Slices.configuration_31_upper_i13
  · exact Slices.configuration_31_upper_i14
  · exact Slices.configuration_31_upper_i15
  · exact Slices.configuration_31_upper_i16
  · exact Slices.configuration_31_upper_i17
  · exact Slices.configuration_31_upper_i18
  · exact Slices.configuration_31_upper_i19
  · exact Slices.configuration_31_upper_i20
  · exact Slices.configuration_31_upper_i21
  · exact Slices.configuration_31_upper_i22
  · exact Slices.configuration_31_upper_i23
  · exact Slices.configuration_31_upper_i24

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_32_lower : ConfigurationValid 32 111 15 := by
  intro i
  fin_cases i
  · exact Slices.configuration_32_lower_i0
  · exact Slices.configuration_32_lower_i1
  · exact Slices.configuration_32_lower_i2
  · exact Slices.configuration_32_lower_i3
  · exact Slices.configuration_32_lower_i4
  · exact Slices.configuration_32_lower_i5
  · exact Slices.configuration_32_lower_i6
  · exact Slices.configuration_32_lower_i7
  · exact Slices.configuration_32_lower_i8
  · exact Slices.configuration_32_lower_i9
  · exact Slices.configuration_32_lower_i10
  · exact Slices.configuration_32_lower_i11
  · exact Slices.configuration_32_lower_i12
  · exact Slices.configuration_32_lower_i13
  · exact Slices.configuration_32_lower_i14
  · exact Slices.configuration_32_lower_i15
  · exact Slices.configuration_32_lower_i16
  · exact Slices.configuration_32_lower_i17
  · exact Slices.configuration_32_lower_i18
  · exact Slices.configuration_32_lower_i19
  · exact Slices.configuration_32_lower_i20
  · exact Slices.configuration_32_lower_i21
  · exact Slices.configuration_32_lower_i22
  · exact Slices.configuration_32_lower_i23
  · exact Slices.configuration_32_lower_i24

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_32_upper : ConfigurationValid 32 111 16 := by
  intro i
  fin_cases i
  · exact Slices.configuration_32_upper_i0
  · exact Slices.configuration_32_upper_i1
  · exact Slices.configuration_32_upper_i2
  · exact Slices.configuration_32_upper_i3
  · exact Slices.configuration_32_upper_i4
  · exact Slices.configuration_32_upper_i5
  · exact Slices.configuration_32_upper_i6
  · exact Slices.configuration_32_upper_i7
  · exact Slices.configuration_32_upper_i8
  · exact Slices.configuration_32_upper_i9
  · exact Slices.configuration_32_upper_i10
  · exact Slices.configuration_32_upper_i11
  · exact Slices.configuration_32_upper_i12
  · exact Slices.configuration_32_upper_i13
  · exact Slices.configuration_32_upper_i14
  · exact Slices.configuration_32_upper_i15
  · exact Slices.configuration_32_upper_i16
  · exact Slices.configuration_32_upper_i17
  · exact Slices.configuration_32_upper_i18
  · exact Slices.configuration_32_upper_i19
  · exact Slices.configuration_32_upper_i20
  · exact Slices.configuration_32_upper_i21
  · exact Slices.configuration_32_upper_i22
  · exact Slices.configuration_32_upper_i23
  · exact Slices.configuration_32_upper_i24
  · exact Slices.configuration_32_upper_i25
  · exact Slices.configuration_32_upper_i26

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_33_lower : ConfigurationValid 33 118 15 := by
  intro i
  fin_cases i
  · exact Slices.configuration_33_lower_i0
  · exact Slices.configuration_33_lower_i1
  · exact Slices.configuration_33_lower_i2
  · exact Slices.configuration_33_lower_i3
  · exact Slices.configuration_33_lower_i4
  · exact Slices.configuration_33_lower_i5
  · exact Slices.configuration_33_lower_i6
  · exact Slices.configuration_33_lower_i7
  · exact Slices.configuration_33_lower_i8
  · exact Slices.configuration_33_lower_i9
  · exact Slices.configuration_33_lower_i10
  · exact Slices.configuration_33_lower_i11
  · exact Slices.configuration_33_lower_i12
  · exact Slices.configuration_33_lower_i13
  · exact Slices.configuration_33_lower_i14
  · exact Slices.configuration_33_lower_i15
  · exact Slices.configuration_33_lower_i16
  · exact Slices.configuration_33_lower_i17
  · exact Slices.configuration_33_lower_i18
  · exact Slices.configuration_33_lower_i19
  · exact Slices.configuration_33_lower_i20
  · exact Slices.configuration_33_lower_i21
  · exact Slices.configuration_33_lower_i22
  · exact Slices.configuration_33_lower_i23
  · exact Slices.configuration_33_lower_i24

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_33_upper : ConfigurationValid 33 118 16 := by
  intro i
  fin_cases i
  · exact Slices.configuration_33_upper_i0
  · exact Slices.configuration_33_upper_i1
  · exact Slices.configuration_33_upper_i2
  · exact Slices.configuration_33_upper_i3
  · exact Slices.configuration_33_upper_i4
  · exact Slices.configuration_33_upper_i5
  · exact Slices.configuration_33_upper_i6
  · exact Slices.configuration_33_upper_i7
  · exact Slices.configuration_33_upper_i8
  · exact Slices.configuration_33_upper_i9
  · exact Slices.configuration_33_upper_i10
  · exact Slices.configuration_33_upper_i11
  · exact Slices.configuration_33_upper_i12
  · exact Slices.configuration_33_upper_i13
  · exact Slices.configuration_33_upper_i14
  · exact Slices.configuration_33_upper_i15
  · exact Slices.configuration_33_upper_i16
  · exact Slices.configuration_33_upper_i17
  · exact Slices.configuration_33_upper_i18
  · exact Slices.configuration_33_upper_i19
  · exact Slices.configuration_33_upper_i20
  · exact Slices.configuration_33_upper_i21
  · exact Slices.configuration_33_upper_i22
  · exact Slices.configuration_33_upper_i23
  · exact Slices.configuration_33_upper_i24
  · exact Slices.configuration_33_upper_i25
  · exact Slices.configuration_33_upper_i26

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_34_lower : ConfigurationValid 34 124 16 := by
  intro i
  fin_cases i
  · exact Slices.configuration_34_lower_i0
  · exact Slices.configuration_34_lower_i1
  · exact Slices.configuration_34_lower_i2
  · exact Slices.configuration_34_lower_i3
  · exact Slices.configuration_34_lower_i4
  · exact Slices.configuration_34_lower_i5
  · exact Slices.configuration_34_lower_i6
  · exact Slices.configuration_34_lower_i7
  · exact Slices.configuration_34_lower_i8
  · exact Slices.configuration_34_lower_i9
  · exact Slices.configuration_34_lower_i10
  · exact Slices.configuration_34_lower_i11
  · exact Slices.configuration_34_lower_i12
  · exact Slices.configuration_34_lower_i13
  · exact Slices.configuration_34_lower_i14
  · exact Slices.configuration_34_lower_i15
  · exact Slices.configuration_34_lower_i16
  · exact Slices.configuration_34_lower_i17
  · exact Slices.configuration_34_lower_i18
  · exact Slices.configuration_34_lower_i19
  · exact Slices.configuration_34_lower_i20
  · exact Slices.configuration_34_lower_i21
  · exact Slices.configuration_34_lower_i22
  · exact Slices.configuration_34_lower_i23
  · exact Slices.configuration_34_lower_i24
  · exact Slices.configuration_34_lower_i25
  · exact Slices.configuration_34_lower_i26

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_34_upper : ConfigurationValid 34 124 17 := by
  intro i
  fin_cases i
  · exact Slices.configuration_34_upper_i0
  · exact Slices.configuration_34_upper_i1
  · exact Slices.configuration_34_upper_i2
  · exact Slices.configuration_34_upper_i3
  · exact Slices.configuration_34_upper_i4
  · exact Slices.configuration_34_upper_i5
  · exact Slices.configuration_34_upper_i6
  · exact Slices.configuration_34_upper_i7
  · exact Slices.configuration_34_upper_i8
  · exact Slices.configuration_34_upper_i9
  · exact Slices.configuration_34_upper_i10
  · exact Slices.configuration_34_upper_i11
  · exact Slices.configuration_34_upper_i12
  · exact Slices.configuration_34_upper_i13
  · exact Slices.configuration_34_upper_i14
  · exact Slices.configuration_34_upper_i15
  · exact Slices.configuration_34_upper_i16
  · exact Slices.configuration_34_upper_i17
  · exact Slices.configuration_34_upper_i18
  · exact Slices.configuration_34_upper_i19
  · exact Slices.configuration_34_upper_i20
  · exact Slices.configuration_34_upper_i21
  · exact Slices.configuration_34_upper_i22
  · exact Slices.configuration_34_upper_i23
  · exact Slices.configuration_34_upper_i24
  · exact Slices.configuration_34_upper_i25
  · exact Slices.configuration_34_upper_i26
  · exact Slices.configuration_34_upper_i27
  · exact Slices.configuration_34_upper_i28

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_35_lower : ConfigurationValid 35 131 17 := by
  intro i
  fin_cases i
  · exact Slices.configuration_35_lower_i0
  · exact Slices.configuration_35_lower_i1
  · exact Slices.configuration_35_lower_i2
  · exact Slices.configuration_35_lower_i3
  · exact Slices.configuration_35_lower_i4
  · exact Slices.configuration_35_lower_i5
  · exact Slices.configuration_35_lower_i6
  · exact Slices.configuration_35_lower_i7
  · exact Slices.configuration_35_lower_i8
  · exact Slices.configuration_35_lower_i9
  · exact Slices.configuration_35_lower_i10
  · exact Slices.configuration_35_lower_i11
  · exact Slices.configuration_35_lower_i12
  · exact Slices.configuration_35_lower_i13
  · exact Slices.configuration_35_lower_i14
  · exact Slices.configuration_35_lower_i15
  · exact Slices.configuration_35_lower_i16
  · exact Slices.configuration_35_lower_i17
  · exact Slices.configuration_35_lower_i18
  · exact Slices.configuration_35_lower_i19
  · exact Slices.configuration_35_lower_i20
  · exact Slices.configuration_35_lower_i21
  · exact Slices.configuration_35_lower_i22
  · exact Slices.configuration_35_lower_i23
  · exact Slices.configuration_35_lower_i24
  · exact Slices.configuration_35_lower_i25
  · exact Slices.configuration_35_lower_i26
  · exact Slices.configuration_35_lower_i27
  · exact Slices.configuration_35_lower_i28

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_35_upper : ConfigurationValid 35 131 18 := by
  intro i
  fin_cases i
  · exact Slices.configuration_35_upper_i0
  · exact Slices.configuration_35_upper_i1
  · exact Slices.configuration_35_upper_i2
  · exact Slices.configuration_35_upper_i3
  · exact Slices.configuration_35_upper_i4
  · exact Slices.configuration_35_upper_i5
  · exact Slices.configuration_35_upper_i6
  · exact Slices.configuration_35_upper_i7
  · exact Slices.configuration_35_upper_i8
  · exact Slices.configuration_35_upper_i9
  · exact Slices.configuration_35_upper_i10
  · exact Slices.configuration_35_upper_i11
  · exact Slices.configuration_35_upper_i12
  · exact Slices.configuration_35_upper_i13
  · exact Slices.configuration_35_upper_i14
  · exact Slices.configuration_35_upper_i15
  · exact Slices.configuration_35_upper_i16
  · exact Slices.configuration_35_upper_i17
  · exact Slices.configuration_35_upper_i18
  · exact Slices.configuration_35_upper_i19
  · exact Slices.configuration_35_upper_i20
  · exact Slices.configuration_35_upper_i21
  · exact Slices.configuration_35_upper_i22
  · exact Slices.configuration_35_upper_i23
  · exact Slices.configuration_35_upper_i24
  · exact Slices.configuration_35_upper_i25
  · exact Slices.configuration_35_upper_i26
  · exact Slices.configuration_35_upper_i27
  · exact Slices.configuration_35_upper_i28
  · exact Slices.configuration_35_upper_i29
  · exact Slices.configuration_35_upper_i30

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_36_lower : ConfigurationValid 36 138 17 := by
  intro i
  fin_cases i
  · exact Slices.configuration_36_lower_i0
  · exact Slices.configuration_36_lower_i1
  · exact Slices.configuration_36_lower_i2
  · exact Slices.configuration_36_lower_i3
  · exact Slices.configuration_36_lower_i4
  · exact Slices.configuration_36_lower_i5
  · exact Slices.configuration_36_lower_i6
  · exact Slices.configuration_36_lower_i7
  · exact Slices.configuration_36_lower_i8
  · exact Slices.configuration_36_lower_i9
  · exact Slices.configuration_36_lower_i10
  · exact Slices.configuration_36_lower_i11
  · exact Slices.configuration_36_lower_i12
  · exact Slices.configuration_36_lower_i13
  · exact Slices.configuration_36_lower_i14
  · exact Slices.configuration_36_lower_i15
  · exact Slices.configuration_36_lower_i16
  · exact Slices.configuration_36_lower_i17
  · exact Slices.configuration_36_lower_i18
  · exact Slices.configuration_36_lower_i19
  · exact Slices.configuration_36_lower_i20
  · exact Slices.configuration_36_lower_i21
  · exact Slices.configuration_36_lower_i22
  · exact Slices.configuration_36_lower_i23
  · exact Slices.configuration_36_lower_i24
  · exact Slices.configuration_36_lower_i25
  · exact Slices.configuration_36_lower_i26
  · exact Slices.configuration_36_lower_i27
  · exact Slices.configuration_36_lower_i28

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_36_upper : ConfigurationValid 36 138 18 := by
  intro i
  fin_cases i
  · exact Slices.configuration_36_upper_i0
  · exact Slices.configuration_36_upper_i1
  · exact Slices.configuration_36_upper_i2
  · exact Slices.configuration_36_upper_i3
  · exact Slices.configuration_36_upper_i4
  · exact Slices.configuration_36_upper_i5
  · exact Slices.configuration_36_upper_i6
  · exact Slices.configuration_36_upper_i7
  · exact Slices.configuration_36_upper_i8
  · exact Slices.configuration_36_upper_i9
  · exact Slices.configuration_36_upper_i10
  · exact Slices.configuration_36_upper_i11
  · exact Slices.configuration_36_upper_i12
  · exact Slices.configuration_36_upper_i13
  · exact Slices.configuration_36_upper_i14
  · exact Slices.configuration_36_upper_i15
  · exact Slices.configuration_36_upper_i16
  · exact Slices.configuration_36_upper_i17
  · exact Slices.configuration_36_upper_i18
  · exact Slices.configuration_36_upper_i19
  · exact Slices.configuration_36_upper_i20
  · exact Slices.configuration_36_upper_i21
  · exact Slices.configuration_36_upper_i22
  · exact Slices.configuration_36_upper_i23
  · exact Slices.configuration_36_upper_i24
  · exact Slices.configuration_36_upper_i25
  · exact Slices.configuration_36_upper_i26
  · exact Slices.configuration_36_upper_i27
  · exact Slices.configuration_36_upper_i28
  · exact Slices.configuration_36_upper_i29
  · exact Slices.configuration_36_upper_i30

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_37_lower : ConfigurationValid 37 145 18 := by
  intro i
  fin_cases i
  · exact Slices.configuration_37_lower_i0
  · exact Slices.configuration_37_lower_i1
  · exact Slices.configuration_37_lower_i2
  · exact Slices.configuration_37_lower_i3
  · exact Slices.configuration_37_lower_i4
  · exact Slices.configuration_37_lower_i5
  · exact Slices.configuration_37_lower_i6
  · exact Slices.configuration_37_lower_i7
  · exact Slices.configuration_37_lower_i8
  · exact Slices.configuration_37_lower_i9
  · exact Slices.configuration_37_lower_i10
  · exact Slices.configuration_37_lower_i11
  · exact Slices.configuration_37_lower_i12
  · exact Slices.configuration_37_lower_i13
  · exact Slices.configuration_37_lower_i14
  · exact Slices.configuration_37_lower_i15
  · exact Slices.configuration_37_lower_i16
  · exact Slices.configuration_37_lower_i17
  · exact Slices.configuration_37_lower_i18
  · exact Slices.configuration_37_lower_i19
  · exact Slices.configuration_37_lower_i20
  · exact Slices.configuration_37_lower_i21
  · exact Slices.configuration_37_lower_i22
  · exact Slices.configuration_37_lower_i23
  · exact Slices.configuration_37_lower_i24
  · exact Slices.configuration_37_lower_i25
  · exact Slices.configuration_37_lower_i26
  · exact Slices.configuration_37_lower_i27
  · exact Slices.configuration_37_lower_i28
  · exact Slices.configuration_37_lower_i29
  · exact Slices.configuration_37_lower_i30

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_37_upper : ConfigurationValid 37 145 19 := by
  intro i
  fin_cases i
  · exact Slices.configuration_37_upper_i0
  · exact Slices.configuration_37_upper_i1
  · exact Slices.configuration_37_upper_i2
  · exact Slices.configuration_37_upper_i3
  · exact Slices.configuration_37_upper_i4
  · exact Slices.configuration_37_upper_i5
  · exact Slices.configuration_37_upper_i6
  · exact Slices.configuration_37_upper_i7
  · exact Slices.configuration_37_upper_i8
  · exact Slices.configuration_37_upper_i9
  · exact Slices.configuration_37_upper_i10
  · exact Slices.configuration_37_upper_i11
  · exact Slices.configuration_37_upper_i12
  · exact Slices.configuration_37_upper_i13
  · exact Slices.configuration_37_upper_i14
  · exact Slices.configuration_37_upper_i15
  · exact Slices.configuration_37_upper_i16
  · exact Slices.configuration_37_upper_i17
  · exact Slices.configuration_37_upper_i18
  · exact Slices.configuration_37_upper_i19
  · exact Slices.configuration_37_upper_i20
  · exact Slices.configuration_37_upper_i21
  · exact Slices.configuration_37_upper_i22
  · exact Slices.configuration_37_upper_i23
  · exact Slices.configuration_37_upper_i24
  · exact Slices.configuration_37_upper_i25
  · exact Slices.configuration_37_upper_i26
  · exact Slices.configuration_37_upper_i27
  · exact Slices.configuration_37_upper_i28
  · exact Slices.configuration_37_upper_i29
  · exact Slices.configuration_37_upper_i30
  · exact Slices.configuration_37_upper_i31
  · exact Slices.configuration_37_upper_i32

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_38_lower : ConfigurationValid 38 153 18 := by
  intro i
  fin_cases i
  · exact Slices.configuration_38_lower_i0
  · exact Slices.configuration_38_lower_i1
  · exact Slices.configuration_38_lower_i2
  · exact Slices.configuration_38_lower_i3
  · exact Slices.configuration_38_lower_i4
  · exact Slices.configuration_38_lower_i5
  · exact Slices.configuration_38_lower_i6
  · exact Slices.configuration_38_lower_i7
  · exact Slices.configuration_38_lower_i8
  · exact Slices.configuration_38_lower_i9
  · exact Slices.configuration_38_lower_i10
  · exact Slices.configuration_38_lower_i11
  · exact Slices.configuration_38_lower_i12
  · exact Slices.configuration_38_lower_i13
  · exact Slices.configuration_38_lower_i14
  · exact Slices.configuration_38_lower_i15
  · exact Slices.configuration_38_lower_i16
  · exact Slices.configuration_38_lower_i17
  · exact Slices.configuration_38_lower_i18
  · exact Slices.configuration_38_lower_i19
  · exact Slices.configuration_38_lower_i20
  · exact Slices.configuration_38_lower_i21
  · exact Slices.configuration_38_lower_i22
  · exact Slices.configuration_38_lower_i23
  · exact Slices.configuration_38_lower_i24
  · exact Slices.configuration_38_lower_i25
  · exact Slices.configuration_38_lower_i26
  · exact Slices.configuration_38_lower_i27
  · exact Slices.configuration_38_lower_i28
  · exact Slices.configuration_38_lower_i29
  · exact Slices.configuration_38_lower_i30

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_38_upper : ConfigurationValid 38 153 19 := by
  intro i
  fin_cases i
  · exact Slices.configuration_38_upper_i0
  · exact Slices.configuration_38_upper_i1
  · exact Slices.configuration_38_upper_i2
  · exact Slices.configuration_38_upper_i3
  · exact Slices.configuration_38_upper_i4
  · exact Slices.configuration_38_upper_i5
  · exact Slices.configuration_38_upper_i6
  · exact Slices.configuration_38_upper_i7
  · exact Slices.configuration_38_upper_i8
  · exact Slices.configuration_38_upper_i9
  · exact Slices.configuration_38_upper_i10
  · exact Slices.configuration_38_upper_i11
  · exact Slices.configuration_38_upper_i12
  · exact Slices.configuration_38_upper_i13
  · exact Slices.configuration_38_upper_i14
  · exact Slices.configuration_38_upper_i15
  · exact Slices.configuration_38_upper_i16
  · exact Slices.configuration_38_upper_i17
  · exact Slices.configuration_38_upper_i18
  · exact Slices.configuration_38_upper_i19
  · exact Slices.configuration_38_upper_i20
  · exact Slices.configuration_38_upper_i21
  · exact Slices.configuration_38_upper_i22
  · exact Slices.configuration_38_upper_i23
  · exact Slices.configuration_38_upper_i24
  · exact Slices.configuration_38_upper_i25
  · exact Slices.configuration_38_upper_i26
  · exact Slices.configuration_38_upper_i27
  · exact Slices.configuration_38_upper_i28
  · exact Slices.configuration_38_upper_i29
  · exact Slices.configuration_38_upper_i30
  · exact Slices.configuration_38_upper_i31
  · exact Slices.configuration_38_upper_i32

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_39_lower : ConfigurationValid 39 160 19 := by
  intro i
  fin_cases i
  · exact Slices.configuration_39_lower_i0
  · exact Slices.configuration_39_lower_i1
  · exact Slices.configuration_39_lower_i2
  · exact Slices.configuration_39_lower_i3
  · exact Slices.configuration_39_lower_i4
  · exact Slices.configuration_39_lower_i5
  · exact Slices.configuration_39_lower_i6
  · exact Slices.configuration_39_lower_i7
  · exact Slices.configuration_39_lower_i8
  · exact Slices.configuration_39_lower_i9
  · exact Slices.configuration_39_lower_i10
  · exact Slices.configuration_39_lower_i11
  · exact Slices.configuration_39_lower_i12
  · exact Slices.configuration_39_lower_i13
  · exact Slices.configuration_39_lower_i14
  · exact Slices.configuration_39_lower_i15
  · exact Slices.configuration_39_lower_i16
  · exact Slices.configuration_39_lower_i17
  · exact Slices.configuration_39_lower_i18
  · exact Slices.configuration_39_lower_i19
  · exact Slices.configuration_39_lower_i20
  · exact Slices.configuration_39_lower_i21
  · exact Slices.configuration_39_lower_i22
  · exact Slices.configuration_39_lower_i23
  · exact Slices.configuration_39_lower_i24
  · exact Slices.configuration_39_lower_i25
  · exact Slices.configuration_39_lower_i26
  · exact Slices.configuration_39_lower_i27
  · exact Slices.configuration_39_lower_i28
  · exact Slices.configuration_39_lower_i29
  · exact Slices.configuration_39_lower_i30
  · exact Slices.configuration_39_lower_i31
  · exact Slices.configuration_39_lower_i32

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_39_upper : ConfigurationValid 39 160 20 := by
  intro i
  fin_cases i
  · exact Slices.configuration_39_upper_i0
  · exact Slices.configuration_39_upper_i1
  · exact Slices.configuration_39_upper_i2
  · exact Slices.configuration_39_upper_i3
  · exact Slices.configuration_39_upper_i4
  · exact Slices.configuration_39_upper_i5
  · exact Slices.configuration_39_upper_i6
  · exact Slices.configuration_39_upper_i7
  · exact Slices.configuration_39_upper_i8
  · exact Slices.configuration_39_upper_i9
  · exact Slices.configuration_39_upper_i10
  · exact Slices.configuration_39_upper_i11
  · exact Slices.configuration_39_upper_i12
  · exact Slices.configuration_39_upper_i13
  · exact Slices.configuration_39_upper_i14
  · exact Slices.configuration_39_upper_i15
  · exact Slices.configuration_39_upper_i16
  · exact Slices.configuration_39_upper_i17
  · exact Slices.configuration_39_upper_i18
  · exact Slices.configuration_39_upper_i19
  · exact Slices.configuration_39_upper_i20
  · exact Slices.configuration_39_upper_i21
  · exact Slices.configuration_39_upper_i22
  · exact Slices.configuration_39_upper_i23
  · exact Slices.configuration_39_upper_i24
  · exact Slices.configuration_39_upper_i25
  · exact Slices.configuration_39_upper_i26
  · exact Slices.configuration_39_upper_i27
  · exact Slices.configuration_39_upper_i28
  · exact Slices.configuration_39_upper_i29
  · exact Slices.configuration_39_upper_i30
  · exact Slices.configuration_39_upper_i31
  · exact Slices.configuration_39_upper_i32
  · exact Slices.configuration_39_upper_i33
  · exact Slices.configuration_39_upper_i34

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_40_lower : ConfigurationValid 40 168 19 := by
  intro i
  fin_cases i
  · exact Slices.configuration_40_lower_i0
  · exact Slices.configuration_40_lower_i1
  · exact Slices.configuration_40_lower_i2
  · exact Slices.configuration_40_lower_i3
  · exact Slices.configuration_40_lower_i4
  · exact Slices.configuration_40_lower_i5
  · exact Slices.configuration_40_lower_i6
  · exact Slices.configuration_40_lower_i7
  · exact Slices.configuration_40_lower_i8
  · exact Slices.configuration_40_lower_i9
  · exact Slices.configuration_40_lower_i10
  · exact Slices.configuration_40_lower_i11
  · exact Slices.configuration_40_lower_i12
  · exact Slices.configuration_40_lower_i13
  · exact Slices.configuration_40_lower_i14
  · exact Slices.configuration_40_lower_i15
  · exact Slices.configuration_40_lower_i16
  · exact Slices.configuration_40_lower_i17
  · exact Slices.configuration_40_lower_i18
  · exact Slices.configuration_40_lower_i19
  · exact Slices.configuration_40_lower_i20
  · exact Slices.configuration_40_lower_i21
  · exact Slices.configuration_40_lower_i22
  · exact Slices.configuration_40_lower_i23
  · exact Slices.configuration_40_lower_i24
  · exact Slices.configuration_40_lower_i25
  · exact Slices.configuration_40_lower_i26
  · exact Slices.configuration_40_lower_i27
  · exact Slices.configuration_40_lower_i28
  · exact Slices.configuration_40_lower_i29
  · exact Slices.configuration_40_lower_i30
  · exact Slices.configuration_40_lower_i31
  · exact Slices.configuration_40_lower_i32

/-- All core-index slices, with the original dependent layer bounds. -/
theorem configuration_40_upper : ConfigurationValid 40 168 20 := by
  intro i
  fin_cases i
  · exact Slices.configuration_40_upper_i0
  · exact Slices.configuration_40_upper_i1
  · exact Slices.configuration_40_upper_i2
  · exact Slices.configuration_40_upper_i3
  · exact Slices.configuration_40_upper_i4
  · exact Slices.configuration_40_upper_i5
  · exact Slices.configuration_40_upper_i6
  · exact Slices.configuration_40_upper_i7
  · exact Slices.configuration_40_upper_i8
  · exact Slices.configuration_40_upper_i9
  · exact Slices.configuration_40_upper_i10
  · exact Slices.configuration_40_upper_i11
  · exact Slices.configuration_40_upper_i12
  · exact Slices.configuration_40_upper_i13
  · exact Slices.configuration_40_upper_i14
  · exact Slices.configuration_40_upper_i15
  · exact Slices.configuration_40_upper_i16
  · exact Slices.configuration_40_upper_i17
  · exact Slices.configuration_40_upper_i18
  · exact Slices.configuration_40_upper_i19
  · exact Slices.configuration_40_upper_i20
  · exact Slices.configuration_40_upper_i21
  · exact Slices.configuration_40_upper_i22
  · exact Slices.configuration_40_upper_i23
  · exact Slices.configuration_40_upper_i24
  · exact Slices.configuration_40_upper_i25
  · exact Slices.configuration_40_upper_i26
  · exact Slices.configuration_40_upper_i27
  · exact Slices.configuration_40_upper_i28
  · exact Slices.configuration_40_upper_i29
  · exact Slices.configuration_40_upper_i30
  · exact Slices.configuration_40_upper_i31
  · exact Slices.configuration_40_upper_i32
  · exact Slices.configuration_40_upper_i33
  · exact Slices.configuration_40_upper_i34

end Quartic.ProfileCertificate
