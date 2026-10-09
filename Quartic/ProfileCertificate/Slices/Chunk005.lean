module

public import Quartic.ProfileCertificate.Slice

@[expose] public section

/-! Bounded kernel checks; each leaf fixes the outer core index. -/

namespace Quartic.ProfileCertificate

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Slices

theorem configuration_28_lower_i5 : ConfigurationSlice 28 87 13 5 := by
  decide +kernel

theorem configuration_28_lower_i13 : ConfigurationSlice 28 87 13 13 := by
  decide +kernel

theorem configuration_28_upper_i0 : ConfigurationSlice 28 87 14 0 := by
  decide +kernel

theorem configuration_28_upper_i8 : ConfigurationSlice 28 87 14 8 := by
  decide +kernel

theorem configuration_28_upper_i16 : ConfigurationSlice 28 87 14 16 := by
  decide +kernel

theorem configuration_29_lower_i1 : ConfigurationSlice 29 93 13 1 := by
  decide +kernel

theorem configuration_29_lower_i9 : ConfigurationSlice 29 93 13 9 := by
  decide +kernel

theorem configuration_29_lower_i17 : ConfigurationSlice 29 93 13 17 := by
  decide +kernel

theorem configuration_29_upper_i4 : ConfigurationSlice 29 93 14 4 := by
  decide +kernel

theorem configuration_29_upper_i12 : ConfigurationSlice 29 93 14 12 := by
  decide +kernel

theorem configuration_29_upper_i20 : ConfigurationSlice 29 93 14 20 := by
  decide +kernel

theorem configuration_30_lower_i5 : ConfigurationSlice 30 99 14 5 := by
  decide +kernel

theorem configuration_30_lower_i13 : ConfigurationSlice 30 99 14 13 := by
  decide +kernel

theorem configuration_30_lower_i21 : ConfigurationSlice 30 99 14 21 := by
  decide +kernel

theorem configuration_30_upper_i6 : ConfigurationSlice 30 99 15 6 := by
  decide +kernel

theorem configuration_30_upper_i14 : ConfigurationSlice 30 99 15 14 := by
  decide +kernel

theorem configuration_30_upper_i22 : ConfigurationSlice 30 99 15 22 := by
  decide +kernel

theorem configuration_31_lower_i5 : ConfigurationSlice 31 105 14 5 := by
  decide +kernel

theorem configuration_31_lower_i13 : ConfigurationSlice 31 105 14 13 := by
  decide +kernel

theorem configuration_31_lower_i21 : ConfigurationSlice 31 105 14 21 := by
  decide +kernel

theorem configuration_31_upper_i6 : ConfigurationSlice 31 105 15 6 := by
  decide +kernel

theorem configuration_31_upper_i14 : ConfigurationSlice 31 105 15 14 := by
  decide +kernel

theorem configuration_31_upper_i22 : ConfigurationSlice 31 105 15 22 := by
  decide +kernel

theorem configuration_32_lower_i5 : ConfigurationSlice 32 111 15 5 := by
  decide +kernel

theorem configuration_32_lower_i13 : ConfigurationSlice 32 111 15 13 := by
  decide +kernel

theorem configuration_32_lower_i21 : ConfigurationSlice 32 111 15 21 := by
  decide +kernel

theorem configuration_32_upper_i4 : ConfigurationSlice 32 111 16 4 := by
  decide +kernel

theorem configuration_32_upper_i12 : ConfigurationSlice 32 111 16 12 := by
  decide +kernel

theorem configuration_32_upper_i20 : ConfigurationSlice 32 111 16 20 := by
  decide +kernel

theorem configuration_33_lower_i1 : ConfigurationSlice 33 118 15 1 := by
  decide +kernel

theorem configuration_33_lower_i9 : ConfigurationSlice 33 118 15 9 := by
  decide +kernel

theorem configuration_33_lower_i17 : ConfigurationSlice 33 118 15 17 := by
  decide +kernel

theorem configuration_33_upper_i0 : ConfigurationSlice 33 118 16 0 := by
  decide +kernel

theorem configuration_33_upper_i8 : ConfigurationSlice 33 118 16 8 := by
  decide +kernel

theorem configuration_33_upper_i16 : ConfigurationSlice 33 118 16 16 := by
  decide +kernel

theorem configuration_33_upper_i24 : ConfigurationSlice 33 118 16 24 := by
  decide +kernel

theorem configuration_34_lower_i5 : ConfigurationSlice 34 124 16 5 := by
  decide +kernel

theorem configuration_34_lower_i13 : ConfigurationSlice 34 124 16 13 := by
  decide +kernel

theorem configuration_34_lower_i21 : ConfigurationSlice 34 124 16 21 := by
  decide +kernel

theorem configuration_34_upper_i2 : ConfigurationSlice 34 124 17 2 := by
  decide +kernel

theorem configuration_34_upper_i10 : ConfigurationSlice 34 124 17 10 := by
  decide +kernel

theorem configuration_34_upper_i18 : ConfigurationSlice 34 124 17 18 := by
  decide +kernel

theorem configuration_34_upper_i26 : ConfigurationSlice 34 124 17 26 := by
  decide +kernel

theorem configuration_35_lower_i5 : ConfigurationSlice 35 131 17 5 := by
  decide +kernel

theorem configuration_35_lower_i13 : ConfigurationSlice 35 131 17 13 := by
  decide +kernel

theorem configuration_35_lower_i21 : ConfigurationSlice 35 131 17 21 := by
  decide +kernel

theorem configuration_35_upper_i0 : ConfigurationSlice 35 131 18 0 := by
  decide +kernel

theorem configuration_35_upper_i8 : ConfigurationSlice 35 131 18 8 := by
  decide +kernel

theorem configuration_35_upper_i16 : ConfigurationSlice 35 131 18 16 := by
  decide +kernel

theorem configuration_35_upper_i24 : ConfigurationSlice 35 131 18 24 := by
  decide +kernel

theorem configuration_36_lower_i1 : ConfigurationSlice 36 138 17 1 := by
  decide +kernel

theorem configuration_36_lower_i9 : ConfigurationSlice 36 138 17 9 := by
  decide +kernel

theorem configuration_36_lower_i17 : ConfigurationSlice 36 138 17 17 := by
  decide +kernel

theorem configuration_36_lower_i25 : ConfigurationSlice 36 138 17 25 := by
  decide +kernel

theorem configuration_36_upper_i4 : ConfigurationSlice 36 138 18 4 := by
  decide +kernel

theorem configuration_36_upper_i12 : ConfigurationSlice 36 138 18 12 := by
  decide +kernel

theorem configuration_36_upper_i20 : ConfigurationSlice 36 138 18 20 := by
  decide +kernel

theorem configuration_36_upper_i28 : ConfigurationSlice 36 138 18 28 := by
  decide +kernel

theorem configuration_37_lower_i5 : ConfigurationSlice 37 145 18 5 := by
  decide +kernel

theorem configuration_37_lower_i13 : ConfigurationSlice 37 145 18 13 := by
  decide +kernel

theorem configuration_37_lower_i21 : ConfigurationSlice 37 145 18 21 := by
  decide +kernel

theorem configuration_37_lower_i29 : ConfigurationSlice 37 145 18 29 := by
  decide +kernel

theorem configuration_37_upper_i6 : ConfigurationSlice 37 145 19 6 := by
  decide +kernel

theorem configuration_37_upper_i14 : ConfigurationSlice 37 145 19 14 := by
  decide +kernel

theorem configuration_37_upper_i22 : ConfigurationSlice 37 145 19 22 := by
  decide +kernel

theorem configuration_37_upper_i30 : ConfigurationSlice 37 145 19 30 := by
  decide +kernel

theorem configuration_38_lower_i5 : ConfigurationSlice 38 153 18 5 := by
  decide +kernel

theorem configuration_38_lower_i13 : ConfigurationSlice 38 153 18 13 := by
  decide +kernel

theorem configuration_38_lower_i21 : ConfigurationSlice 38 153 18 21 := by
  decide +kernel

theorem configuration_38_lower_i29 : ConfigurationSlice 38 153 18 29 := by
  decide +kernel

theorem configuration_38_upper_i6 : ConfigurationSlice 38 153 19 6 := by
  decide +kernel

theorem configuration_38_upper_i14 : ConfigurationSlice 38 153 19 14 := by
  decide +kernel

theorem configuration_38_upper_i22 : ConfigurationSlice 38 153 19 22 := by
  decide +kernel

theorem configuration_38_upper_i30 : ConfigurationSlice 38 153 19 30 := by
  decide +kernel

theorem configuration_39_lower_i5 : ConfigurationSlice 39 160 19 5 := by
  decide +kernel

theorem configuration_39_lower_i13 : ConfigurationSlice 39 160 19 13 := by
  decide +kernel

theorem configuration_39_lower_i21 : ConfigurationSlice 39 160 19 21 := by
  decide +kernel

theorem configuration_39_lower_i29 : ConfigurationSlice 39 160 19 29 := by
  decide +kernel

theorem configuration_39_upper_i4 : ConfigurationSlice 39 160 20 4 := by
  decide +kernel

theorem configuration_39_upper_i12 : ConfigurationSlice 39 160 20 12 := by
  decide +kernel

theorem configuration_39_upper_i20 : ConfigurationSlice 39 160 20 20 := by
  decide +kernel

theorem configuration_39_upper_i28 : ConfigurationSlice 39 160 20 28 := by
  decide +kernel

theorem configuration_40_lower_i1 : ConfigurationSlice 40 168 19 1 := by
  decide +kernel

theorem configuration_40_lower_i9 : ConfigurationSlice 40 168 19 9 := by
  decide +kernel

theorem configuration_40_lower_i17 : ConfigurationSlice 40 168 19 17 := by
  decide +kernel

theorem configuration_40_lower_i25 : ConfigurationSlice 40 168 19 25 := by
  decide +kernel

theorem configuration_40_upper_i0 : ConfigurationSlice 40 168 20 0 := by
  decide +kernel

theorem configuration_40_upper_i8 : ConfigurationSlice 40 168 20 8 := by
  decide +kernel

theorem configuration_40_upper_i16 : ConfigurationSlice 40 168 20 16 := by
  decide +kernel

theorem configuration_40_upper_i24 : ConfigurationSlice 40 168 20 24 := by
  decide +kernel

theorem configuration_40_upper_i32 : ConfigurationSlice 40 168 20 32 := by
  decide +kernel

end Slices

end Quartic.ProfileCertificate
