module

public import Quartic.ProfileCertificate.Slice

@[expose] public section

/-! Bounded kernel checks; each leaf fixes the outer core index. -/

namespace Quartic.ProfileCertificate

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Slices

theorem configuration_28_lower_i0 : ConfigurationSlice 28 87 13 0 := by
  decide +kernel

theorem configuration_28_lower_i8 : ConfigurationSlice 28 87 13 8 := by
  decide +kernel

theorem configuration_28_lower_i16 : ConfigurationSlice 28 87 13 16 := by
  decide +kernel

theorem configuration_28_upper_i3 : ConfigurationSlice 28 87 14 3 := by
  decide +kernel

theorem configuration_28_upper_i11 : ConfigurationSlice 28 87 14 11 := by
  decide +kernel

theorem configuration_28_upper_i19 : ConfigurationSlice 28 87 14 19 := by
  decide +kernel

theorem configuration_29_lower_i4 : ConfigurationSlice 29 93 13 4 := by
  decide +kernel

theorem configuration_29_lower_i12 : ConfigurationSlice 29 93 13 12 := by
  decide +kernel

theorem configuration_29_lower_i20 : ConfigurationSlice 29 93 13 20 := by
  decide +kernel

theorem configuration_29_upper_i7 : ConfigurationSlice 29 93 14 7 := by
  decide +kernel

theorem configuration_29_upper_i15 : ConfigurationSlice 29 93 14 15 := by
  decide +kernel

theorem configuration_30_lower_i0 : ConfigurationSlice 30 99 14 0 := by
  decide +kernel

theorem configuration_30_lower_i8 : ConfigurationSlice 30 99 14 8 := by
  decide +kernel

theorem configuration_30_lower_i16 : ConfigurationSlice 30 99 14 16 := by
  decide +kernel

theorem configuration_30_upper_i1 : ConfigurationSlice 30 99 15 1 := by
  decide +kernel

theorem configuration_30_upper_i9 : ConfigurationSlice 30 99 15 9 := by
  decide +kernel

theorem configuration_30_upper_i17 : ConfigurationSlice 30 99 15 17 := by
  decide +kernel

theorem configuration_31_lower_i0 : ConfigurationSlice 31 105 14 0 := by
  decide +kernel

theorem configuration_31_lower_i8 : ConfigurationSlice 31 105 14 8 := by
  decide +kernel

theorem configuration_31_lower_i16 : ConfigurationSlice 31 105 14 16 := by
  decide +kernel

theorem configuration_31_upper_i1 : ConfigurationSlice 31 105 15 1 := by
  decide +kernel

theorem configuration_31_upper_i9 : ConfigurationSlice 31 105 15 9 := by
  decide +kernel

theorem configuration_31_upper_i17 : ConfigurationSlice 31 105 15 17 := by
  decide +kernel

theorem configuration_32_lower_i0 : ConfigurationSlice 32 111 15 0 := by
  decide +kernel

theorem configuration_32_lower_i8 : ConfigurationSlice 32 111 15 8 := by
  decide +kernel

theorem configuration_32_lower_i16 : ConfigurationSlice 32 111 15 16 := by
  decide +kernel

theorem configuration_32_lower_i24 : ConfigurationSlice 32 111 15 24 := by
  decide +kernel

theorem configuration_32_upper_i7 : ConfigurationSlice 32 111 16 7 := by
  decide +kernel

theorem configuration_32_upper_i15 : ConfigurationSlice 32 111 16 15 := by
  decide +kernel

theorem configuration_32_upper_i23 : ConfigurationSlice 32 111 16 23 := by
  decide +kernel

theorem configuration_33_lower_i4 : ConfigurationSlice 33 118 15 4 := by
  decide +kernel

theorem configuration_33_lower_i12 : ConfigurationSlice 33 118 15 12 := by
  decide +kernel

theorem configuration_33_lower_i20 : ConfigurationSlice 33 118 15 20 := by
  decide +kernel

theorem configuration_33_upper_i3 : ConfigurationSlice 33 118 16 3 := by
  decide +kernel

theorem configuration_33_upper_i11 : ConfigurationSlice 33 118 16 11 := by
  decide +kernel

theorem configuration_33_upper_i19 : ConfigurationSlice 33 118 16 19 := by
  decide +kernel

theorem configuration_34_lower_i0 : ConfigurationSlice 34 124 16 0 := by
  decide +kernel

theorem configuration_34_lower_i8 : ConfigurationSlice 34 124 16 8 := by
  decide +kernel

theorem configuration_34_lower_i16 : ConfigurationSlice 34 124 16 16 := by
  decide +kernel

theorem configuration_34_lower_i24 : ConfigurationSlice 34 124 16 24 := by
  decide +kernel

theorem configuration_34_upper_i5 : ConfigurationSlice 34 124 17 5 := by
  decide +kernel

theorem configuration_34_upper_i13 : ConfigurationSlice 34 124 17 13 := by
  decide +kernel

theorem configuration_34_upper_i21 : ConfigurationSlice 34 124 17 21 := by
  decide +kernel

theorem configuration_35_lower_i0 : ConfigurationSlice 35 131 17 0 := by
  decide +kernel

theorem configuration_35_lower_i8 : ConfigurationSlice 35 131 17 8 := by
  decide +kernel

theorem configuration_35_lower_i16 : ConfigurationSlice 35 131 17 16 := by
  decide +kernel

theorem configuration_35_lower_i24 : ConfigurationSlice 35 131 17 24 := by
  decide +kernel

theorem configuration_35_upper_i3 : ConfigurationSlice 35 131 18 3 := by
  decide +kernel

theorem configuration_35_upper_i11 : ConfigurationSlice 35 131 18 11 := by
  decide +kernel

theorem configuration_35_upper_i19 : ConfigurationSlice 35 131 18 19 := by
  decide +kernel

theorem configuration_35_upper_i27 : ConfigurationSlice 35 131 18 27 := by
  decide +kernel

theorem configuration_36_lower_i4 : ConfigurationSlice 36 138 17 4 := by
  decide +kernel

theorem configuration_36_lower_i12 : ConfigurationSlice 36 138 17 12 := by
  decide +kernel

theorem configuration_36_lower_i20 : ConfigurationSlice 36 138 17 20 := by
  decide +kernel

theorem configuration_36_lower_i28 : ConfigurationSlice 36 138 17 28 := by
  decide +kernel

theorem configuration_36_upper_i7 : ConfigurationSlice 36 138 18 7 := by
  decide +kernel

theorem configuration_36_upper_i15 : ConfigurationSlice 36 138 18 15 := by
  decide +kernel

theorem configuration_36_upper_i23 : ConfigurationSlice 36 138 18 23 := by
  decide +kernel

theorem configuration_37_lower_i0 : ConfigurationSlice 37 145 18 0 := by
  decide +kernel

theorem configuration_37_lower_i8 : ConfigurationSlice 37 145 18 8 := by
  decide +kernel

theorem configuration_37_lower_i16 : ConfigurationSlice 37 145 18 16 := by
  decide +kernel

theorem configuration_37_lower_i24 : ConfigurationSlice 37 145 18 24 := by
  decide +kernel

theorem configuration_37_upper_i1 : ConfigurationSlice 37 145 19 1 := by
  decide +kernel

theorem configuration_37_upper_i9 : ConfigurationSlice 37 145 19 9 := by
  decide +kernel

theorem configuration_37_upper_i17 : ConfigurationSlice 37 145 19 17 := by
  decide +kernel

theorem configuration_37_upper_i25 : ConfigurationSlice 37 145 19 25 := by
  decide +kernel

theorem configuration_38_lower_i0 : ConfigurationSlice 38 153 18 0 := by
  decide +kernel

theorem configuration_38_lower_i8 : ConfigurationSlice 38 153 18 8 := by
  decide +kernel

theorem configuration_38_lower_i16 : ConfigurationSlice 38 153 18 16 := by
  decide +kernel

theorem configuration_38_lower_i24 : ConfigurationSlice 38 153 18 24 := by
  decide +kernel

theorem configuration_38_upper_i1 : ConfigurationSlice 38 153 19 1 := by
  decide +kernel

theorem configuration_38_upper_i9 : ConfigurationSlice 38 153 19 9 := by
  decide +kernel

theorem configuration_38_upper_i17 : ConfigurationSlice 38 153 19 17 := by
  decide +kernel

theorem configuration_38_upper_i25 : ConfigurationSlice 38 153 19 25 := by
  decide +kernel

theorem configuration_39_lower_i0 : ConfigurationSlice 39 160 19 0 := by
  decide +kernel

theorem configuration_39_lower_i8 : ConfigurationSlice 39 160 19 8 := by
  decide +kernel

theorem configuration_39_lower_i16 : ConfigurationSlice 39 160 19 16 := by
  decide +kernel

theorem configuration_39_lower_i24 : ConfigurationSlice 39 160 19 24 := by
  decide +kernel

theorem configuration_39_lower_i32 : ConfigurationSlice 39 160 19 32 := by
  decide +kernel

theorem configuration_39_upper_i7 : ConfigurationSlice 39 160 20 7 := by
  decide +kernel

theorem configuration_39_upper_i15 : ConfigurationSlice 39 160 20 15 := by
  decide +kernel

theorem configuration_39_upper_i23 : ConfigurationSlice 39 160 20 23 := by
  decide +kernel

theorem configuration_39_upper_i31 : ConfigurationSlice 39 160 20 31 := by
  decide +kernel

theorem configuration_40_lower_i4 : ConfigurationSlice 40 168 19 4 := by
  decide +kernel

theorem configuration_40_lower_i12 : ConfigurationSlice 40 168 19 12 := by
  decide +kernel

theorem configuration_40_lower_i20 : ConfigurationSlice 40 168 19 20 := by
  decide +kernel

theorem configuration_40_lower_i28 : ConfigurationSlice 40 168 19 28 := by
  decide +kernel

theorem configuration_40_upper_i3 : ConfigurationSlice 40 168 20 3 := by
  decide +kernel

theorem configuration_40_upper_i11 : ConfigurationSlice 40 168 20 11 := by
  decide +kernel

theorem configuration_40_upper_i19 : ConfigurationSlice 40 168 20 19 := by
  decide +kernel

theorem configuration_40_upper_i27 : ConfigurationSlice 40 168 20 27 := by
  decide +kernel

end Slices

end Quartic.ProfileCertificate
