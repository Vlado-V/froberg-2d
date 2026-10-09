module

public import Quartic.ProfileCertificate.Slice

@[expose] public section

/-! Bounded kernel checks; each leaf fixes the outer core index. -/

namespace Quartic.ProfileCertificate

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Slices

theorem configuration_28_lower_i4 : ConfigurationSlice 28 87 13 4 := by
  decide +kernel

theorem configuration_28_lower_i12 : ConfigurationSlice 28 87 13 12 := by
  decide +kernel

theorem configuration_28_lower_i20 : ConfigurationSlice 28 87 13 20 := by
  decide +kernel

theorem configuration_28_upper_i7 : ConfigurationSlice 28 87 14 7 := by
  decide +kernel

theorem configuration_28_upper_i15 : ConfigurationSlice 28 87 14 15 := by
  decide +kernel

theorem configuration_29_lower_i0 : ConfigurationSlice 29 93 13 0 := by
  decide +kernel

theorem configuration_29_lower_i8 : ConfigurationSlice 29 93 13 8 := by
  decide +kernel

theorem configuration_29_lower_i16 : ConfigurationSlice 29 93 13 16 := by
  decide +kernel

theorem configuration_29_upper_i3 : ConfigurationSlice 29 93 14 3 := by
  decide +kernel

theorem configuration_29_upper_i11 : ConfigurationSlice 29 93 14 11 := by
  decide +kernel

theorem configuration_29_upper_i19 : ConfigurationSlice 29 93 14 19 := by
  decide +kernel

theorem configuration_30_lower_i4 : ConfigurationSlice 30 99 14 4 := by
  decide +kernel

theorem configuration_30_lower_i12 : ConfigurationSlice 30 99 14 12 := by
  decide +kernel

theorem configuration_30_lower_i20 : ConfigurationSlice 30 99 14 20 := by
  decide +kernel

theorem configuration_30_upper_i5 : ConfigurationSlice 30 99 15 5 := by
  decide +kernel

theorem configuration_30_upper_i13 : ConfigurationSlice 30 99 15 13 := by
  decide +kernel

theorem configuration_30_upper_i21 : ConfigurationSlice 30 99 15 21 := by
  decide +kernel

theorem configuration_31_lower_i4 : ConfigurationSlice 31 105 14 4 := by
  decide +kernel

theorem configuration_31_lower_i12 : ConfigurationSlice 31 105 14 12 := by
  decide +kernel

theorem configuration_31_lower_i20 : ConfigurationSlice 31 105 14 20 := by
  decide +kernel

theorem configuration_31_upper_i5 : ConfigurationSlice 31 105 15 5 := by
  decide +kernel

theorem configuration_31_upper_i13 : ConfigurationSlice 31 105 15 13 := by
  decide +kernel

theorem configuration_31_upper_i21 : ConfigurationSlice 31 105 15 21 := by
  decide +kernel

theorem configuration_32_lower_i4 : ConfigurationSlice 32 111 15 4 := by
  decide +kernel

theorem configuration_32_lower_i12 : ConfigurationSlice 32 111 15 12 := by
  decide +kernel

theorem configuration_32_lower_i20 : ConfigurationSlice 32 111 15 20 := by
  decide +kernel

theorem configuration_32_upper_i3 : ConfigurationSlice 32 111 16 3 := by
  decide +kernel

theorem configuration_32_upper_i11 : ConfigurationSlice 32 111 16 11 := by
  decide +kernel

theorem configuration_32_upper_i19 : ConfigurationSlice 32 111 16 19 := by
  decide +kernel

theorem configuration_33_lower_i0 : ConfigurationSlice 33 118 15 0 := by
  decide +kernel

theorem configuration_33_lower_i8 : ConfigurationSlice 33 118 15 8 := by
  decide +kernel

theorem configuration_33_lower_i16 : ConfigurationSlice 33 118 15 16 := by
  decide +kernel

theorem configuration_33_lower_i24 : ConfigurationSlice 33 118 15 24 := by
  decide +kernel

theorem configuration_33_upper_i7 : ConfigurationSlice 33 118 16 7 := by
  decide +kernel

theorem configuration_33_upper_i15 : ConfigurationSlice 33 118 16 15 := by
  decide +kernel

theorem configuration_33_upper_i23 : ConfigurationSlice 33 118 16 23 := by
  decide +kernel

theorem configuration_34_lower_i4 : ConfigurationSlice 34 124 16 4 := by
  decide +kernel

theorem configuration_34_lower_i12 : ConfigurationSlice 34 124 16 12 := by
  decide +kernel

theorem configuration_34_lower_i20 : ConfigurationSlice 34 124 16 20 := by
  decide +kernel

theorem configuration_34_upper_i1 : ConfigurationSlice 34 124 17 1 := by
  decide +kernel

theorem configuration_34_upper_i9 : ConfigurationSlice 34 124 17 9 := by
  decide +kernel

theorem configuration_34_upper_i17 : ConfigurationSlice 34 124 17 17 := by
  decide +kernel

theorem configuration_34_upper_i25 : ConfigurationSlice 34 124 17 25 := by
  decide +kernel

theorem configuration_35_lower_i4 : ConfigurationSlice 35 131 17 4 := by
  decide +kernel

theorem configuration_35_lower_i12 : ConfigurationSlice 35 131 17 12 := by
  decide +kernel

theorem configuration_35_lower_i20 : ConfigurationSlice 35 131 17 20 := by
  decide +kernel

theorem configuration_35_lower_i28 : ConfigurationSlice 35 131 17 28 := by
  decide +kernel

theorem configuration_35_upper_i7 : ConfigurationSlice 35 131 18 7 := by
  decide +kernel

theorem configuration_35_upper_i15 : ConfigurationSlice 35 131 18 15 := by
  decide +kernel

theorem configuration_35_upper_i23 : ConfigurationSlice 35 131 18 23 := by
  decide +kernel

theorem configuration_36_lower_i0 : ConfigurationSlice 36 138 17 0 := by
  decide +kernel

theorem configuration_36_lower_i8 : ConfigurationSlice 36 138 17 8 := by
  decide +kernel

theorem configuration_36_lower_i16 : ConfigurationSlice 36 138 17 16 := by
  decide +kernel

theorem configuration_36_lower_i24 : ConfigurationSlice 36 138 17 24 := by
  decide +kernel

theorem configuration_36_upper_i3 : ConfigurationSlice 36 138 18 3 := by
  decide +kernel

theorem configuration_36_upper_i11 : ConfigurationSlice 36 138 18 11 := by
  decide +kernel

theorem configuration_36_upper_i19 : ConfigurationSlice 36 138 18 19 := by
  decide +kernel

theorem configuration_36_upper_i27 : ConfigurationSlice 36 138 18 27 := by
  decide +kernel

theorem configuration_37_lower_i4 : ConfigurationSlice 37 145 18 4 := by
  decide +kernel

theorem configuration_37_lower_i12 : ConfigurationSlice 37 145 18 12 := by
  decide +kernel

theorem configuration_37_lower_i20 : ConfigurationSlice 37 145 18 20 := by
  decide +kernel

theorem configuration_37_lower_i28 : ConfigurationSlice 37 145 18 28 := by
  decide +kernel

theorem configuration_37_upper_i5 : ConfigurationSlice 37 145 19 5 := by
  decide +kernel

theorem configuration_37_upper_i13 : ConfigurationSlice 37 145 19 13 := by
  decide +kernel

theorem configuration_37_upper_i21 : ConfigurationSlice 37 145 19 21 := by
  decide +kernel

theorem configuration_37_upper_i29 : ConfigurationSlice 37 145 19 29 := by
  decide +kernel

theorem configuration_38_lower_i4 : ConfigurationSlice 38 153 18 4 := by
  decide +kernel

theorem configuration_38_lower_i12 : ConfigurationSlice 38 153 18 12 := by
  decide +kernel

theorem configuration_38_lower_i20 : ConfigurationSlice 38 153 18 20 := by
  decide +kernel

theorem configuration_38_lower_i28 : ConfigurationSlice 38 153 18 28 := by
  decide +kernel

theorem configuration_38_upper_i5 : ConfigurationSlice 38 153 19 5 := by
  decide +kernel

theorem configuration_38_upper_i13 : ConfigurationSlice 38 153 19 13 := by
  decide +kernel

theorem configuration_38_upper_i21 : ConfigurationSlice 38 153 19 21 := by
  decide +kernel

theorem configuration_38_upper_i29 : ConfigurationSlice 38 153 19 29 := by
  decide +kernel

theorem configuration_39_lower_i4 : ConfigurationSlice 39 160 19 4 := by
  decide +kernel

theorem configuration_39_lower_i12 : ConfigurationSlice 39 160 19 12 := by
  decide +kernel

theorem configuration_39_lower_i20 : ConfigurationSlice 39 160 19 20 := by
  decide +kernel

theorem configuration_39_lower_i28 : ConfigurationSlice 39 160 19 28 := by
  decide +kernel

theorem configuration_39_upper_i3 : ConfigurationSlice 39 160 20 3 := by
  decide +kernel

theorem configuration_39_upper_i11 : ConfigurationSlice 39 160 20 11 := by
  decide +kernel

theorem configuration_39_upper_i19 : ConfigurationSlice 39 160 20 19 := by
  decide +kernel

theorem configuration_39_upper_i27 : ConfigurationSlice 39 160 20 27 := by
  decide +kernel

theorem configuration_40_lower_i0 : ConfigurationSlice 40 168 19 0 := by
  decide +kernel

theorem configuration_40_lower_i8 : ConfigurationSlice 40 168 19 8 := by
  decide +kernel

theorem configuration_40_lower_i16 : ConfigurationSlice 40 168 19 16 := by
  decide +kernel

theorem configuration_40_lower_i24 : ConfigurationSlice 40 168 19 24 := by
  decide +kernel

theorem configuration_40_lower_i32 : ConfigurationSlice 40 168 19 32 := by
  decide +kernel

theorem configuration_40_upper_i7 : ConfigurationSlice 40 168 20 7 := by
  decide +kernel

theorem configuration_40_upper_i15 : ConfigurationSlice 40 168 20 15 := by
  decide +kernel

theorem configuration_40_upper_i23 : ConfigurationSlice 40 168 20 23 := by
  decide +kernel

theorem configuration_40_upper_i31 : ConfigurationSlice 40 168 20 31 := by
  decide +kernel

end Slices

end Quartic.ProfileCertificate
