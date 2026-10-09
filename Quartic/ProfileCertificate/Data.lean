module

public import Quartic.ProfileCertificate.Slices.Chunk000
public import Quartic.ProfileCertificate.Slices.Chunk001
public import Quartic.ProfileCertificate.Slices.Chunk002
public import Quartic.ProfileCertificate.Slices.Chunk003
public import Quartic.ProfileCertificate.Slices.Chunk004
public import Quartic.ProfileCertificate.Slices.Chunk005
public import Quartic.ProfileCertificate.Slices.Chunk006
public import Quartic.ProfileCertificate.Slices.Chunk007

@[expose] public section

/-! Assemble the original profile statements from eight independently checked modules. -/

namespace Quartic.ProfileCertificate

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


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
