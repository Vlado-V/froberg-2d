module

public import Quartic.ProfileCertificate.Slice

@[expose] public section

/-! Bounded kernel checks; each leaf fixes the outer core index. -/

namespace Quartic.ProfileCertificate

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Slices

theorem configuration_28_lower_i7 : ConfigurationSlice 28 87 13 7 := by
  decide +kernel

theorem configuration_28_lower_i15 : ConfigurationSlice 28 87 13 15 := by
  decide +kernel

theorem configuration_28_upper_i2 : ConfigurationSlice 28 87 14 2 := by
  decide +kernel

theorem configuration_28_upper_i10 : ConfigurationSlice 28 87 14 10 := by
  decide +kernel

theorem configuration_28_upper_i18 : ConfigurationSlice 28 87 14 18 := by
  decide +kernel

theorem configuration_29_lower_i3 : ConfigurationSlice 29 93 13 3 := by
  decide +kernel

theorem configuration_29_lower_i11 : ConfigurationSlice 29 93 13 11 := by
  decide +kernel

theorem configuration_29_lower_i19 : ConfigurationSlice 29 93 13 19 := by
  decide +kernel

theorem configuration_29_upper_i6 : ConfigurationSlice 29 93 14 6 := by
  decide +kernel

theorem configuration_29_upper_i14 : ConfigurationSlice 29 93 14 14 := by
  decide +kernel

theorem configuration_29_upper_i22 : ConfigurationSlice 29 93 14 22 := by
  decide +kernel

theorem configuration_30_lower_i7 : ConfigurationSlice 30 99 14 7 := by
  decide +kernel

theorem configuration_30_lower_i15 : ConfigurationSlice 30 99 14 15 := by
  decide +kernel

theorem configuration_30_upper_i0 : ConfigurationSlice 30 99 15 0 := by
  decide +kernel

theorem configuration_30_upper_i8 : ConfigurationSlice 30 99 15 8 := by
  decide +kernel

theorem configuration_30_upper_i16 : ConfigurationSlice 30 99 15 16 := by
  decide +kernel

theorem configuration_30_upper_i24 : ConfigurationSlice 30 99 15 24 := by
  decide +kernel

theorem configuration_31_lower_i7 : ConfigurationSlice 31 105 14 7 := by
  decide +kernel

theorem configuration_31_lower_i15 : ConfigurationSlice 31 105 14 15 := by
  decide +kernel

theorem configuration_31_upper_i0 : ConfigurationSlice 31 105 15 0 := by
  decide +kernel

theorem configuration_31_upper_i8 : ConfigurationSlice 31 105 15 8 := by
  decide +kernel

theorem configuration_31_upper_i16 : ConfigurationSlice 31 105 15 16 := by
  decide +kernel

theorem configuration_31_upper_i24 : ConfigurationSlice 31 105 15 24 := by
  decide +kernel

theorem configuration_32_lower_i7 : ConfigurationSlice 32 111 15 7 := by
  decide +kernel

theorem configuration_32_lower_i15 : ConfigurationSlice 32 111 15 15 := by
  decide +kernel

theorem configuration_32_lower_i23 : ConfigurationSlice 32 111 15 23 := by
  decide +kernel

theorem configuration_32_upper_i6 : ConfigurationSlice 32 111 16 6 := by
  decide +kernel

theorem configuration_32_upper_i14 : ConfigurationSlice 32 111 16 14 := by
  decide +kernel

theorem configuration_32_upper_i22 : ConfigurationSlice 32 111 16 22 := by
  decide +kernel

theorem configuration_33_lower_i3 : ConfigurationSlice 33 118 15 3 := by
  decide +kernel

theorem configuration_33_lower_i11 : ConfigurationSlice 33 118 15 11 := by
  decide +kernel

theorem configuration_33_lower_i19 : ConfigurationSlice 33 118 15 19 := by
  decide +kernel

theorem configuration_33_upper_i2 : ConfigurationSlice 33 118 16 2 := by
  decide +kernel

theorem configuration_33_upper_i10 : ConfigurationSlice 33 118 16 10 := by
  decide +kernel

theorem configuration_33_upper_i18 : ConfigurationSlice 33 118 16 18 := by
  decide +kernel

theorem configuration_33_upper_i26 : ConfigurationSlice 33 118 16 26 := by
  decide +kernel

theorem configuration_34_lower_i7 : ConfigurationSlice 34 124 16 7 := by
  decide +kernel

theorem configuration_34_lower_i15 : ConfigurationSlice 34 124 16 15 := by
  decide +kernel

theorem configuration_34_lower_i23 : ConfigurationSlice 34 124 16 23 := by
  decide +kernel

theorem configuration_34_upper_i4 : ConfigurationSlice 34 124 17 4 := by
  decide +kernel

theorem configuration_34_upper_i12 : ConfigurationSlice 34 124 17 12 := by
  decide +kernel

theorem configuration_34_upper_i20 : ConfigurationSlice 34 124 17 20 := by
  decide +kernel

theorem configuration_34_upper_i28 : ConfigurationSlice 34 124 17 28 := by
  decide +kernel

theorem configuration_35_lower_i7 : ConfigurationSlice 35 131 17 7 := by
  decide +kernel

theorem configuration_35_lower_i15 : ConfigurationSlice 35 131 17 15 := by
  decide +kernel

theorem configuration_35_lower_i23 : ConfigurationSlice 35 131 17 23 := by
  decide +kernel

theorem configuration_35_upper_i2 : ConfigurationSlice 35 131 18 2 := by
  decide +kernel

theorem configuration_35_upper_i10 : ConfigurationSlice 35 131 18 10 := by
  decide +kernel

theorem configuration_35_upper_i18 : ConfigurationSlice 35 131 18 18 := by
  decide +kernel

theorem configuration_35_upper_i26 : ConfigurationSlice 35 131 18 26 := by
  decide +kernel

theorem configuration_36_lower_i3 : ConfigurationSlice 36 138 17 3 := by
  decide +kernel

theorem configuration_36_lower_i11 : ConfigurationSlice 36 138 17 11 := by
  decide +kernel

theorem configuration_36_lower_i19 : ConfigurationSlice 36 138 17 19 := by
  decide +kernel

theorem configuration_36_lower_i27 : ConfigurationSlice 36 138 17 27 := by
  decide +kernel

theorem configuration_36_upper_i6 : ConfigurationSlice 36 138 18 6 := by
  decide +kernel

theorem configuration_36_upper_i14 : ConfigurationSlice 36 138 18 14 := by
  decide +kernel

theorem configuration_36_upper_i22 : ConfigurationSlice 36 138 18 22 := by
  decide +kernel

theorem configuration_36_upper_i30 : ConfigurationSlice 36 138 18 30 := by
  decide +kernel

theorem configuration_37_lower_i7 : ConfigurationSlice 37 145 18 7 := by
  decide +kernel

theorem configuration_37_lower_i15 : ConfigurationSlice 37 145 18 15 := by
  decide +kernel

theorem configuration_37_lower_i23 : ConfigurationSlice 37 145 18 23 := by
  decide +kernel

theorem configuration_37_upper_i0 : ConfigurationSlice 37 145 19 0 := by
  decide +kernel

theorem configuration_37_upper_i8 : ConfigurationSlice 37 145 19 8 := by
  decide +kernel

theorem configuration_37_upper_i16 : ConfigurationSlice 37 145 19 16 := by
  decide +kernel

theorem configuration_37_upper_i24 : ConfigurationSlice 37 145 19 24 := by
  decide +kernel

theorem configuration_37_upper_i32 : ConfigurationSlice 37 145 19 32 := by
  decide +kernel

theorem configuration_38_lower_i7 : ConfigurationSlice 38 153 18 7 := by
  decide +kernel

theorem configuration_38_lower_i15 : ConfigurationSlice 38 153 18 15 := by
  decide +kernel

theorem configuration_38_lower_i23 : ConfigurationSlice 38 153 18 23 := by
  decide +kernel

theorem configuration_38_upper_i0 : ConfigurationSlice 38 153 19 0 := by
  decide +kernel

theorem configuration_38_upper_i8 : ConfigurationSlice 38 153 19 8 := by
  decide +kernel

theorem configuration_38_upper_i16 : ConfigurationSlice 38 153 19 16 := by
  decide +kernel

theorem configuration_38_upper_i24 : ConfigurationSlice 38 153 19 24 := by
  decide +kernel

theorem configuration_38_upper_i32 : ConfigurationSlice 38 153 19 32 := by
  decide +kernel

theorem configuration_39_lower_i7 : ConfigurationSlice 39 160 19 7 := by
  decide +kernel

theorem configuration_39_lower_i15 : ConfigurationSlice 39 160 19 15 := by
  decide +kernel

theorem configuration_39_lower_i23 : ConfigurationSlice 39 160 19 23 := by
  decide +kernel

theorem configuration_39_lower_i31 : ConfigurationSlice 39 160 19 31 := by
  decide +kernel

theorem configuration_39_upper_i6 : ConfigurationSlice 39 160 20 6 := by
  decide +kernel

theorem configuration_39_upper_i14 : ConfigurationSlice 39 160 20 14 := by
  decide +kernel

theorem configuration_39_upper_i22 : ConfigurationSlice 39 160 20 22 := by
  decide +kernel

theorem configuration_39_upper_i30 : ConfigurationSlice 39 160 20 30 := by
  decide +kernel

theorem configuration_40_lower_i3 : ConfigurationSlice 40 168 19 3 := by
  decide +kernel

theorem configuration_40_lower_i11 : ConfigurationSlice 40 168 19 11 := by
  decide +kernel

theorem configuration_40_lower_i19 : ConfigurationSlice 40 168 19 19 := by
  decide +kernel

theorem configuration_40_lower_i27 : ConfigurationSlice 40 168 19 27 := by
  decide +kernel

theorem configuration_40_upper_i2 : ConfigurationSlice 40 168 20 2 := by
  decide +kernel

theorem configuration_40_upper_i10 : ConfigurationSlice 40 168 20 10 := by
  decide +kernel

theorem configuration_40_upper_i18 : ConfigurationSlice 40 168 20 18 := by
  decide +kernel

theorem configuration_40_upper_i26 : ConfigurationSlice 40 168 20 26 := by
  decide +kernel

theorem configuration_40_upper_i34 : ConfigurationSlice 40 168 20 34 := by
  decide +kernel

end Slices

end Quartic.ProfileCertificate
