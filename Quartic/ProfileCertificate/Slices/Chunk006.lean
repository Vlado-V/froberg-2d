module

public import Quartic.ProfileCertificate.Slice

@[expose] public section

/-! Bounded kernel checks; each leaf fixes the outer core index. -/

namespace Quartic.ProfileCertificate

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Slices

theorem configuration_28_lower_i6 : ConfigurationSlice 28 87 13 6 := by
  decide +kernel

theorem configuration_28_lower_i14 : ConfigurationSlice 28 87 13 14 := by
  decide +kernel

theorem configuration_28_upper_i1 : ConfigurationSlice 28 87 14 1 := by
  decide +kernel

theorem configuration_28_upper_i9 : ConfigurationSlice 28 87 14 9 := by
  decide +kernel

theorem configuration_28_upper_i17 : ConfigurationSlice 28 87 14 17 := by
  decide +kernel

theorem configuration_29_lower_i2 : ConfigurationSlice 29 93 13 2 := by
  decide +kernel

theorem configuration_29_lower_i10 : ConfigurationSlice 29 93 13 10 := by
  decide +kernel

theorem configuration_29_lower_i18 : ConfigurationSlice 29 93 13 18 := by
  decide +kernel

theorem configuration_29_upper_i5 : ConfigurationSlice 29 93 14 5 := by
  decide +kernel

theorem configuration_29_upper_i13 : ConfigurationSlice 29 93 14 13 := by
  decide +kernel

theorem configuration_29_upper_i21 : ConfigurationSlice 29 93 14 21 := by
  decide +kernel

theorem configuration_30_lower_i6 : ConfigurationSlice 30 99 14 6 := by
  decide +kernel

theorem configuration_30_lower_i14 : ConfigurationSlice 30 99 14 14 := by
  decide +kernel

theorem configuration_30_lower_i22 : ConfigurationSlice 30 99 14 22 := by
  decide +kernel

theorem configuration_30_upper_i7 : ConfigurationSlice 30 99 15 7 := by
  decide +kernel

theorem configuration_30_upper_i15 : ConfigurationSlice 30 99 15 15 := by
  decide +kernel

theorem configuration_30_upper_i23 : ConfigurationSlice 30 99 15 23 := by
  decide +kernel

theorem configuration_31_lower_i6 : ConfigurationSlice 31 105 14 6 := by
  decide +kernel

theorem configuration_31_lower_i14 : ConfigurationSlice 31 105 14 14 := by
  decide +kernel

theorem configuration_31_lower_i22 : ConfigurationSlice 31 105 14 22 := by
  decide +kernel

theorem configuration_31_upper_i7 : ConfigurationSlice 31 105 15 7 := by
  decide +kernel

theorem configuration_31_upper_i15 : ConfigurationSlice 31 105 15 15 := by
  decide +kernel

theorem configuration_31_upper_i23 : ConfigurationSlice 31 105 15 23 := by
  decide +kernel

theorem configuration_32_lower_i6 : ConfigurationSlice 32 111 15 6 := by
  decide +kernel

theorem configuration_32_lower_i14 : ConfigurationSlice 32 111 15 14 := by
  decide +kernel

theorem configuration_32_lower_i22 : ConfigurationSlice 32 111 15 22 := by
  decide +kernel

theorem configuration_32_upper_i5 : ConfigurationSlice 32 111 16 5 := by
  decide +kernel

theorem configuration_32_upper_i13 : ConfigurationSlice 32 111 16 13 := by
  decide +kernel

theorem configuration_32_upper_i21 : ConfigurationSlice 32 111 16 21 := by
  decide +kernel

theorem configuration_33_lower_i2 : ConfigurationSlice 33 118 15 2 := by
  decide +kernel

theorem configuration_33_lower_i10 : ConfigurationSlice 33 118 15 10 := by
  decide +kernel

theorem configuration_33_lower_i18 : ConfigurationSlice 33 118 15 18 := by
  decide +kernel

theorem configuration_33_upper_i1 : ConfigurationSlice 33 118 16 1 := by
  decide +kernel

theorem configuration_33_upper_i9 : ConfigurationSlice 33 118 16 9 := by
  decide +kernel

theorem configuration_33_upper_i17 : ConfigurationSlice 33 118 16 17 := by
  decide +kernel

theorem configuration_33_upper_i25 : ConfigurationSlice 33 118 16 25 := by
  decide +kernel

theorem configuration_34_lower_i6 : ConfigurationSlice 34 124 16 6 := by
  decide +kernel

theorem configuration_34_lower_i14 : ConfigurationSlice 34 124 16 14 := by
  decide +kernel

theorem configuration_34_lower_i22 : ConfigurationSlice 34 124 16 22 := by
  decide +kernel

theorem configuration_34_upper_i3 : ConfigurationSlice 34 124 17 3 := by
  decide +kernel

theorem configuration_34_upper_i11 : ConfigurationSlice 34 124 17 11 := by
  decide +kernel

theorem configuration_34_upper_i19 : ConfigurationSlice 34 124 17 19 := by
  decide +kernel

theorem configuration_34_upper_i27 : ConfigurationSlice 34 124 17 27 := by
  decide +kernel

theorem configuration_35_lower_i6 : ConfigurationSlice 35 131 17 6 := by
  decide +kernel

theorem configuration_35_lower_i14 : ConfigurationSlice 35 131 17 14 := by
  decide +kernel

theorem configuration_35_lower_i22 : ConfigurationSlice 35 131 17 22 := by
  decide +kernel

theorem configuration_35_upper_i1 : ConfigurationSlice 35 131 18 1 := by
  decide +kernel

theorem configuration_35_upper_i9 : ConfigurationSlice 35 131 18 9 := by
  decide +kernel

theorem configuration_35_upper_i17 : ConfigurationSlice 35 131 18 17 := by
  decide +kernel

theorem configuration_35_upper_i25 : ConfigurationSlice 35 131 18 25 := by
  decide +kernel

theorem configuration_36_lower_i2 : ConfigurationSlice 36 138 17 2 := by
  decide +kernel

theorem configuration_36_lower_i10 : ConfigurationSlice 36 138 17 10 := by
  decide +kernel

theorem configuration_36_lower_i18 : ConfigurationSlice 36 138 17 18 := by
  decide +kernel

theorem configuration_36_lower_i26 : ConfigurationSlice 36 138 17 26 := by
  decide +kernel

theorem configuration_36_upper_i5 : ConfigurationSlice 36 138 18 5 := by
  decide +kernel

theorem configuration_36_upper_i13 : ConfigurationSlice 36 138 18 13 := by
  decide +kernel

theorem configuration_36_upper_i21 : ConfigurationSlice 36 138 18 21 := by
  decide +kernel

theorem configuration_36_upper_i29 : ConfigurationSlice 36 138 18 29 := by
  decide +kernel

theorem configuration_37_lower_i6 : ConfigurationSlice 37 145 18 6 := by
  decide +kernel

theorem configuration_37_lower_i14 : ConfigurationSlice 37 145 18 14 := by
  decide +kernel

theorem configuration_37_lower_i22 : ConfigurationSlice 37 145 18 22 := by
  decide +kernel

theorem configuration_37_lower_i30 : ConfigurationSlice 37 145 18 30 := by
  decide +kernel

theorem configuration_37_upper_i7 : ConfigurationSlice 37 145 19 7 := by
  decide +kernel

theorem configuration_37_upper_i15 : ConfigurationSlice 37 145 19 15 := by
  decide +kernel

theorem configuration_37_upper_i23 : ConfigurationSlice 37 145 19 23 := by
  decide +kernel

theorem configuration_37_upper_i31 : ConfigurationSlice 37 145 19 31 := by
  decide +kernel

theorem configuration_38_lower_i6 : ConfigurationSlice 38 153 18 6 := by
  decide +kernel

theorem configuration_38_lower_i14 : ConfigurationSlice 38 153 18 14 := by
  decide +kernel

theorem configuration_38_lower_i22 : ConfigurationSlice 38 153 18 22 := by
  decide +kernel

theorem configuration_38_lower_i30 : ConfigurationSlice 38 153 18 30 := by
  decide +kernel

theorem configuration_38_upper_i7 : ConfigurationSlice 38 153 19 7 := by
  decide +kernel

theorem configuration_38_upper_i15 : ConfigurationSlice 38 153 19 15 := by
  decide +kernel

theorem configuration_38_upper_i23 : ConfigurationSlice 38 153 19 23 := by
  decide +kernel

theorem configuration_38_upper_i31 : ConfigurationSlice 38 153 19 31 := by
  decide +kernel

theorem configuration_39_lower_i6 : ConfigurationSlice 39 160 19 6 := by
  decide +kernel

theorem configuration_39_lower_i14 : ConfigurationSlice 39 160 19 14 := by
  decide +kernel

theorem configuration_39_lower_i22 : ConfigurationSlice 39 160 19 22 := by
  decide +kernel

theorem configuration_39_lower_i30 : ConfigurationSlice 39 160 19 30 := by
  decide +kernel

theorem configuration_39_upper_i5 : ConfigurationSlice 39 160 20 5 := by
  decide +kernel

theorem configuration_39_upper_i13 : ConfigurationSlice 39 160 20 13 := by
  decide +kernel

theorem configuration_39_upper_i21 : ConfigurationSlice 39 160 20 21 := by
  decide +kernel

theorem configuration_39_upper_i29 : ConfigurationSlice 39 160 20 29 := by
  decide +kernel

theorem configuration_40_lower_i2 : ConfigurationSlice 40 168 19 2 := by
  decide +kernel

theorem configuration_40_lower_i10 : ConfigurationSlice 40 168 19 10 := by
  decide +kernel

theorem configuration_40_lower_i18 : ConfigurationSlice 40 168 19 18 := by
  decide +kernel

theorem configuration_40_lower_i26 : ConfigurationSlice 40 168 19 26 := by
  decide +kernel

theorem configuration_40_upper_i1 : ConfigurationSlice 40 168 20 1 := by
  decide +kernel

theorem configuration_40_upper_i9 : ConfigurationSlice 40 168 20 9 := by
  decide +kernel

theorem configuration_40_upper_i17 : ConfigurationSlice 40 168 20 17 := by
  decide +kernel

theorem configuration_40_upper_i25 : ConfigurationSlice 40 168 20 25 := by
  decide +kernel

theorem configuration_40_upper_i33 : ConfigurationSlice 40 168 20 33 := by
  decide +kernel

end Slices

end Quartic.ProfileCertificate
