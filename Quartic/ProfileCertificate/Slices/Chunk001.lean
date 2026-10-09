module

public import Quartic.ProfileCertificate.Slice

@[expose] public section

/-! Bounded kernel checks; each leaf fixes the outer core index. -/

namespace Quartic.ProfileCertificate

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Slices

theorem configuration_28_lower_i1 : ConfigurationSlice 28 87 13 1 := by
  decide +kernel

theorem configuration_28_lower_i9 : ConfigurationSlice 28 87 13 9 := by
  decide +kernel

theorem configuration_28_lower_i17 : ConfigurationSlice 28 87 13 17 := by
  decide +kernel

theorem configuration_28_upper_i4 : ConfigurationSlice 28 87 14 4 := by
  decide +kernel

theorem configuration_28_upper_i12 : ConfigurationSlice 28 87 14 12 := by
  decide +kernel

theorem configuration_28_upper_i20 : ConfigurationSlice 28 87 14 20 := by
  decide +kernel

theorem configuration_29_lower_i5 : ConfigurationSlice 29 93 13 5 := by
  decide +kernel

theorem configuration_29_lower_i13 : ConfigurationSlice 29 93 13 13 := by
  decide +kernel

theorem configuration_29_upper_i0 : ConfigurationSlice 29 93 14 0 := by
  decide +kernel

theorem configuration_29_upper_i8 : ConfigurationSlice 29 93 14 8 := by
  decide +kernel

theorem configuration_29_upper_i16 : ConfigurationSlice 29 93 14 16 := by
  decide +kernel

theorem configuration_30_lower_i1 : ConfigurationSlice 30 99 14 1 := by
  decide +kernel

theorem configuration_30_lower_i9 : ConfigurationSlice 30 99 14 9 := by
  decide +kernel

theorem configuration_30_lower_i17 : ConfigurationSlice 30 99 14 17 := by
  decide +kernel

theorem configuration_30_upper_i2 : ConfigurationSlice 30 99 15 2 := by
  decide +kernel

theorem configuration_30_upper_i10 : ConfigurationSlice 30 99 15 10 := by
  decide +kernel

theorem configuration_30_upper_i18 : ConfigurationSlice 30 99 15 18 := by
  decide +kernel

theorem configuration_31_lower_i1 : ConfigurationSlice 31 105 14 1 := by
  decide +kernel

theorem configuration_31_lower_i9 : ConfigurationSlice 31 105 14 9 := by
  decide +kernel

theorem configuration_31_lower_i17 : ConfigurationSlice 31 105 14 17 := by
  decide +kernel

theorem configuration_31_upper_i2 : ConfigurationSlice 31 105 15 2 := by
  decide +kernel

theorem configuration_31_upper_i10 : ConfigurationSlice 31 105 15 10 := by
  decide +kernel

theorem configuration_31_upper_i18 : ConfigurationSlice 31 105 15 18 := by
  decide +kernel

theorem configuration_32_lower_i1 : ConfigurationSlice 32 111 15 1 := by
  decide +kernel

theorem configuration_32_lower_i9 : ConfigurationSlice 32 111 15 9 := by
  decide +kernel

theorem configuration_32_lower_i17 : ConfigurationSlice 32 111 15 17 := by
  decide +kernel

theorem configuration_32_upper_i0 : ConfigurationSlice 32 111 16 0 := by
  decide +kernel

theorem configuration_32_upper_i8 : ConfigurationSlice 32 111 16 8 := by
  decide +kernel

theorem configuration_32_upper_i16 : ConfigurationSlice 32 111 16 16 := by
  decide +kernel

theorem configuration_32_upper_i24 : ConfigurationSlice 32 111 16 24 := by
  decide +kernel

theorem configuration_33_lower_i5 : ConfigurationSlice 33 118 15 5 := by
  decide +kernel

theorem configuration_33_lower_i13 : ConfigurationSlice 33 118 15 13 := by
  decide +kernel

theorem configuration_33_lower_i21 : ConfigurationSlice 33 118 15 21 := by
  decide +kernel

theorem configuration_33_upper_i4 : ConfigurationSlice 33 118 16 4 := by
  decide +kernel

theorem configuration_33_upper_i12 : ConfigurationSlice 33 118 16 12 := by
  decide +kernel

theorem configuration_33_upper_i20 : ConfigurationSlice 33 118 16 20 := by
  decide +kernel

theorem configuration_34_lower_i1 : ConfigurationSlice 34 124 16 1 := by
  decide +kernel

theorem configuration_34_lower_i9 : ConfigurationSlice 34 124 16 9 := by
  decide +kernel

theorem configuration_34_lower_i17 : ConfigurationSlice 34 124 16 17 := by
  decide +kernel

theorem configuration_34_lower_i25 : ConfigurationSlice 34 124 16 25 := by
  decide +kernel

theorem configuration_34_upper_i6 : ConfigurationSlice 34 124 17 6 := by
  decide +kernel

theorem configuration_34_upper_i14 : ConfigurationSlice 34 124 17 14 := by
  decide +kernel

theorem configuration_34_upper_i22 : ConfigurationSlice 34 124 17 22 := by
  decide +kernel

theorem configuration_35_lower_i1 : ConfigurationSlice 35 131 17 1 := by
  decide +kernel

theorem configuration_35_lower_i9 : ConfigurationSlice 35 131 17 9 := by
  decide +kernel

theorem configuration_35_lower_i17 : ConfigurationSlice 35 131 17 17 := by
  decide +kernel

theorem configuration_35_lower_i25 : ConfigurationSlice 35 131 17 25 := by
  decide +kernel

theorem configuration_35_upper_i4 : ConfigurationSlice 35 131 18 4 := by
  decide +kernel

theorem configuration_35_upper_i12 : ConfigurationSlice 35 131 18 12 := by
  decide +kernel

theorem configuration_35_upper_i20 : ConfigurationSlice 35 131 18 20 := by
  decide +kernel

theorem configuration_35_upper_i28 : ConfigurationSlice 35 131 18 28 := by
  decide +kernel

theorem configuration_36_lower_i5 : ConfigurationSlice 36 138 17 5 := by
  decide +kernel

theorem configuration_36_lower_i13 : ConfigurationSlice 36 138 17 13 := by
  decide +kernel

theorem configuration_36_lower_i21 : ConfigurationSlice 36 138 17 21 := by
  decide +kernel

theorem configuration_36_upper_i0 : ConfigurationSlice 36 138 18 0 := by
  decide +kernel

theorem configuration_36_upper_i8 : ConfigurationSlice 36 138 18 8 := by
  decide +kernel

theorem configuration_36_upper_i16 : ConfigurationSlice 36 138 18 16 := by
  decide +kernel

theorem configuration_36_upper_i24 : ConfigurationSlice 36 138 18 24 := by
  decide +kernel

theorem configuration_37_lower_i1 : ConfigurationSlice 37 145 18 1 := by
  decide +kernel

theorem configuration_37_lower_i9 : ConfigurationSlice 37 145 18 9 := by
  decide +kernel

theorem configuration_37_lower_i17 : ConfigurationSlice 37 145 18 17 := by
  decide +kernel

theorem configuration_37_lower_i25 : ConfigurationSlice 37 145 18 25 := by
  decide +kernel

theorem configuration_37_upper_i2 : ConfigurationSlice 37 145 19 2 := by
  decide +kernel

theorem configuration_37_upper_i10 : ConfigurationSlice 37 145 19 10 := by
  decide +kernel

theorem configuration_37_upper_i18 : ConfigurationSlice 37 145 19 18 := by
  decide +kernel

theorem configuration_37_upper_i26 : ConfigurationSlice 37 145 19 26 := by
  decide +kernel

theorem configuration_38_lower_i1 : ConfigurationSlice 38 153 18 1 := by
  decide +kernel

theorem configuration_38_lower_i9 : ConfigurationSlice 38 153 18 9 := by
  decide +kernel

theorem configuration_38_lower_i17 : ConfigurationSlice 38 153 18 17 := by
  decide +kernel

theorem configuration_38_lower_i25 : ConfigurationSlice 38 153 18 25 := by
  decide +kernel

theorem configuration_38_upper_i2 : ConfigurationSlice 38 153 19 2 := by
  decide +kernel

theorem configuration_38_upper_i10 : ConfigurationSlice 38 153 19 10 := by
  decide +kernel

theorem configuration_38_upper_i18 : ConfigurationSlice 38 153 19 18 := by
  decide +kernel

theorem configuration_38_upper_i26 : ConfigurationSlice 38 153 19 26 := by
  decide +kernel

theorem configuration_39_lower_i1 : ConfigurationSlice 39 160 19 1 := by
  decide +kernel

theorem configuration_39_lower_i9 : ConfigurationSlice 39 160 19 9 := by
  decide +kernel

theorem configuration_39_lower_i17 : ConfigurationSlice 39 160 19 17 := by
  decide +kernel

theorem configuration_39_lower_i25 : ConfigurationSlice 39 160 19 25 := by
  decide +kernel

theorem configuration_39_upper_i0 : ConfigurationSlice 39 160 20 0 := by
  decide +kernel

theorem configuration_39_upper_i8 : ConfigurationSlice 39 160 20 8 := by
  decide +kernel

theorem configuration_39_upper_i16 : ConfigurationSlice 39 160 20 16 := by
  decide +kernel

theorem configuration_39_upper_i24 : ConfigurationSlice 39 160 20 24 := by
  decide +kernel

theorem configuration_39_upper_i32 : ConfigurationSlice 39 160 20 32 := by
  decide +kernel

theorem configuration_40_lower_i5 : ConfigurationSlice 40 168 19 5 := by
  decide +kernel

theorem configuration_40_lower_i13 : ConfigurationSlice 40 168 19 13 := by
  decide +kernel

theorem configuration_40_lower_i21 : ConfigurationSlice 40 168 19 21 := by
  decide +kernel

theorem configuration_40_lower_i29 : ConfigurationSlice 40 168 19 29 := by
  decide +kernel

theorem configuration_40_upper_i4 : ConfigurationSlice 40 168 20 4 := by
  decide +kernel

theorem configuration_40_upper_i12 : ConfigurationSlice 40 168 20 12 := by
  decide +kernel

theorem configuration_40_upper_i20 : ConfigurationSlice 40 168 20 20 := by
  decide +kernel

theorem configuration_40_upper_i28 : ConfigurationSlice 40 168 20 28 := by
  decide +kernel

end Slices

end Quartic.ProfileCertificate
