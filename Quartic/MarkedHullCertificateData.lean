module

public import Quartic.MarkedHullCertificateCore

@[expose] public section

/-! The ordinary lower-endpoint interval witnesses, rechecked for the stronger
marked inequality. These are literal copies of the lower data in
`HullCertificate.Data`; all modified assertions are checked by the kernel. -/

namespace Quartic.MarkedHullCertificate

open Quartic.HullCertificate

private def data_130_lower : Array (List Chunk) := #[
  [⟨1, 99, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨100, 107, ⟨0, 3, false, true, false, 100, 100⟩⟩,
   ⟨108, 225, ⟨3, 7, false, true, false, 108, 108⟩⟩,
   ⟨226, 233, ⟨3, 7, false, false, false, 226, 226⟩⟩],
  [⟨44, 99, ⟨0, 3, true, true, false, 99, 99⟩⟩,
   ⟨100, 129, ⟨0, 3, false, true, false, 129, 129⟩⟩,
   ⟨130, 225, ⟨3, 7, false, true, false, 130, 130⟩⟩,
   ⟨226, 255, ⟨3, 7, false, false, false, 226, 226⟩⟩],
  [⟨66, 99, ⟨0, 2, true, true, false, 99, 99⟩⟩,
   ⟨100, 129, ⟨0, 2, false, true, false, 129, 129⟩⟩,
   ⟨130, 225, ⟨2, 7, false, true, false, 130, 130⟩⟩,
   ⟨226, 277, ⟨2, 7, false, false, false, 226, 226⟩⟩],
  [⟨88, 99, ⟨0, 2, true, true, false, 99, 99⟩⟩,
   ⟨100, 151, ⟨0, 2, false, true, false, 151, 151⟩⟩,
   ⟨152, 225, ⟨2, 7, false, true, false, 225, 225⟩⟩,
   ⟨226, 320, ⟨2, 7, false, false, false, 315, 315⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_130_lower : ConfigurationBounds 130 1617 69 := by
  apply configuration_of_cells 130 1617 69 data_130_lower
  decide +kernel

private def data_131_lower : Array (List Chunk) := #[
  [⟨1, 100, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨101, 107, ⟨0, 3, false, true, false, 101, 101⟩⟩,
   ⟨108, 182, ⟨3, 7, false, true, false, 108, 108⟩⟩,
   ⟨183, 233, ⟨3, 7, false, false, false, 183, 183⟩⟩],
  [⟨45, 100, ⟨0, 3, true, true, false, 100, 100⟩⟩,
   ⟨101, 130, ⟨0, 3, false, true, false, 130, 130⟩⟩,
   ⟨131, 182, ⟨3, 7, false, true, false, 131, 131⟩⟩,
   ⟨183, 256, ⟨3, 7, false, false, false, 183, 183⟩⟩],
  [⟨67, 100, ⟨0, 2, true, true, false, 100, 100⟩⟩,
   ⟨101, 130, ⟨0, 2, false, true, false, 130, 130⟩⟩,
   ⟨131, 182, ⟨2, 7, false, true, false, 131, 131⟩⟩,
   ⟨183, 278, ⟨2, 7, false, false, false, 183, 183⟩⟩],
  [⟨90, 100, ⟨0, 2, true, true, false, 100, 100⟩⟩,
   ⟨101, 152, ⟨0, 2, false, true, false, 152, 152⟩⟩,
   ⟨153, 182, ⟨2, 7, false, true, false, 182, 182⟩⟩,
   ⟨183, 322, ⟨2, 7, false, false, false, 322, 322⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_131_lower : ConfigurationBounds 131 1641 70 := by
  apply configuration_of_cells 131 1641 70 data_131_lower
  decide +kernel

private def data_132_lower : Array (List Chunk) := #[
  [⟨1, 100, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨101, 108, ⟨0, 3, false, true, false, 101, 101⟩⟩,
   ⟨109, 220, ⟨3, 7, false, true, false, 109, 109⟩⟩,
   ⟨221, 236, ⟨3, 7, false, false, false, 221, 221⟩⟩],
  [⟨45, 100, ⟨0, 3, true, true, false, 100, 100⟩⟩,
   ⟨101, 131, ⟨0, 3, false, true, false, 131, 131⟩⟩,
   ⟨132, 220, ⟨3, 7, false, true, false, 132, 132⟩⟩,
   ⟨221, 259, ⟨3, 7, false, false, false, 221, 221⟩⟩],
  [⟨67, 100, ⟨0, 2, true, true, false, 100, 100⟩⟩,
   ⟨101, 131, ⟨0, 2, false, true, false, 131, 131⟩⟩,
   ⟨132, 220, ⟨2, 7, false, true, false, 132, 132⟩⟩,
   ⟨221, 281, ⟨2, 7, false, false, false, 221, 221⟩⟩],
  [⟨90, 100, ⟨0, 2, true, true, false, 100, 100⟩⟩,
   ⟨101, 153, ⟨0, 2, false, true, false, 153, 153⟩⟩,
   ⟨154, 220, ⟨2, 7, false, true, false, 220, 220⟩⟩,
   ⟨221, 325, ⟨2, 7, false, false, false, 321, 321⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_132_lower : ConfigurationBounds 132 1666 70 := by
  apply configuration_of_cells 132 1666 70 data_132_lower
  decide +kernel

private def data_133_lower : Array (List Chunk) := #[
  [⟨1, 101, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨102, 109, ⟨0, 3, false, true, false, 102, 102⟩⟩,
   ⟨110, 239, ⟨3, 7, false, true, false, 110, 110⟩⟩],
  [⟨45, 101, ⟨0, 3, true, true, false, 101, 101⟩⟩,
   ⟨102, 132, ⟨0, 3, false, true, false, 132, 132⟩⟩,
   ⟨133, 240, ⟨3, 7, false, true, false, 133, 133⟩⟩,
   ⟨241, 262, ⟨3, 7, false, false, false, 241, 241⟩⟩],
  [⟨67, 101, ⟨0, 2, true, true, false, 101, 101⟩⟩,
   ⟨102, 132, ⟨0, 2, false, true, false, 132, 132⟩⟩,
   ⟨133, 240, ⟨2, 7, false, true, false, 133, 133⟩⟩,
   ⟨241, 284, ⟨2, 7, false, false, false, 241, 241⟩⟩],
  [⟨90, 101, ⟨0, 2, true, true, false, 101, 101⟩⟩,
   ⟨102, 154, ⟨0, 2, false, true, false, 154, 154⟩⟩,
   ⟨155, 240, ⟨2, 7, false, true, false, 240, 240⟩⟩,
   ⟨241, 328, ⟨2, 7, false, false, false, 320, 320⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_133_lower : ConfigurationBounds 133 1691 70 := by
  apply configuration_of_cells 133 1691 70 data_133_lower
  decide +kernel

private def data_134_lower : Array (List Chunk) := #[
  [⟨1, 102, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨103, 110, ⟨0, 3, false, true, false, 103, 103⟩⟩,
   ⟨111, 240, ⟨3, 7, false, true, false, 111, 111⟩⟩],
  [⟨46, 102, ⟨0, 3, true, true, false, 102, 102⟩⟩,
   ⟨103, 133, ⟨0, 3, false, true, false, 133, 133⟩⟩,
   ⟨134, 243, ⟨3, 7, false, true, false, 134, 134⟩⟩,
   ⟨244, 263, ⟨3, 7, false, false, false, 244, 244⟩⟩],
  [⟨68, 102, ⟨0, 2, true, true, false, 102, 102⟩⟩,
   ⟨103, 133, ⟨0, 2, false, true, false, 133, 133⟩⟩,
   ⟨134, 243, ⟨2, 7, false, true, false, 134, 134⟩⟩,
   ⟨244, 285, ⟨2, 7, false, false, false, 244, 244⟩⟩],
  [⟨91, 102, ⟨0, 2, true, true, false, 102, 102⟩⟩,
   ⟨103, 155, ⟨0, 2, false, true, false, 155, 155⟩⟩,
   ⟨156, 243, ⟨2, 7, false, true, false, 243, 243⟩⟩,
   ⟨244, 330, ⟨2, 7, false, false, false, 328, 328⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_134_lower : ConfigurationBounds 134 1716 71 := by
  apply configuration_of_cells 134 1716 71 data_134_lower
  decide +kernel

private def data_135_lower : Array (List Chunk) := #[
  [⟨1, 103, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨104, 111, ⟨0, 3, false, true, false, 104, 104⟩⟩,
   ⟨112, 227, ⟨3, 7, false, true, false, 112, 112⟩⟩,
   ⟨228, 241, ⟨3, 7, false, false, false, 228, 228⟩⟩],
  [⟨46, 103, ⟨0, 3, true, true, false, 103, 103⟩⟩,
   ⟨104, 134, ⟨0, 3, false, true, false, 134, 134⟩⟩,
   ⟨135, 227, ⟨3, 7, false, true, false, 135, 135⟩⟩,
   ⟨228, 264, ⟨3, 7, false, false, false, 228, 228⟩⟩],
  [⟨69, 103, ⟨0, 2, true, true, false, 103, 103⟩⟩,
   ⟨104, 134, ⟨0, 2, false, true, false, 134, 134⟩⟩,
   ⟨135, 227, ⟨2, 7, false, true, false, 135, 135⟩⟩,
   ⟨228, 287, ⟨2, 7, false, false, false, 228, 228⟩⟩],
  [⟨92, 103, ⟨0, 2, true, true, false, 103, 103⟩⟩,
   ⟨104, 157, ⟨0, 2, false, true, false, 157, 157⟩⟩,
   ⟨158, 227, ⟨2, 7, false, true, false, 227, 227⟩⟩,
   ⟨228, 332, ⟨2, 7, false, false, false, 332, 332⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_135_lower : ConfigurationBounds 135 1741 72 := by
  apply configuration_of_cells 135 1741 72 data_135_lower
  decide +kernel

private def data_136_lower : Array (List Chunk) := #[
  [⟨1, 103, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨104, 112, ⟨0, 3, false, true, false, 104, 104⟩⟩,
   ⟨113, 189, ⟨3, 7, false, true, false, 113, 113⟩⟩,
   ⟨190, 244, ⟨3, 7, false, false, false, 190, 190⟩⟩],
  [⟨46, 103, ⟨0, 3, true, true, false, 103, 103⟩⟩,
   ⟨104, 135, ⟨0, 3, false, true, false, 135, 135⟩⟩,
   ⟨136, 189, ⟨3, 7, false, true, false, 136, 136⟩⟩,
   ⟨190, 267, ⟨3, 7, false, false, false, 190, 190⟩⟩],
  [⟨69, 103, ⟨0, 2, true, true, false, 103, 103⟩⟩,
   ⟨104, 135, ⟨0, 2, false, true, false, 135, 135⟩⟩,
   ⟨136, 189, ⟨2, 7, false, true, false, 136, 136⟩⟩,
   ⟨190, 290, ⟨2, 7, false, false, false, 190, 190⟩⟩],
  [⟨92, 103, ⟨0, 2, true, true, false, 103, 103⟩⟩,
   ⟨104, 158, ⟨0, 2, false, true, false, 158, 158⟩⟩,
   ⟨159, 189, ⟨2, 7, false, true, false, 189, 189⟩⟩,
   ⟨190, 335, ⟨2, 7, false, false, false, 335, 335⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_136_lower : ConfigurationBounds 136 1766 72 := by
  apply configuration_of_cells 136 1766 72 data_136_lower
  decide +kernel

private def data_137_lower : Array (List Chunk) := #[
  [⟨1, 104, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨105, 112, ⟨0, 3, false, true, false, 105, 105⟩⟩,
   ⟨113, 239, ⟨3, 7, false, true, false, 113, 113⟩⟩,
   ⟨240, 244, ⟨3, 7, false, false, false, 240, 240⟩⟩],
  [⟨47, 104, ⟨0, 3, true, true, false, 104, 104⟩⟩,
   ⟨105, 136, ⟨0, 3, false, true, false, 136, 136⟩⟩,
   ⟨137, 239, ⟨3, 7, false, true, false, 137, 137⟩⟩,
   ⟨240, 268, ⟨3, 7, false, false, false, 240, 240⟩⟩],
  [⟨70, 104, ⟨0, 2, true, true, false, 104, 104⟩⟩,
   ⟨105, 136, ⟨0, 2, false, true, false, 136, 136⟩⟩,
   ⟨137, 239, ⟨2, 7, false, true, false, 137, 137⟩⟩,
   ⟨240, 291, ⟨2, 7, false, false, false, 240, 240⟩⟩],
  [⟨94, 104, ⟨0, 2, true, true, false, 104, 104⟩⟩,
   ⟨105, 159, ⟨0, 2, false, true, false, 159, 159⟩⟩,
   ⟨160, 239, ⟨2, 7, false, true, false, 239, 239⟩⟩,
   ⟨240, 337, ⟨2, 7, false, false, false, 337, 337⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_137_lower : ConfigurationBounds 137 1792 73 := by
  apply configuration_of_cells 137 1792 73 data_137_lower
  decide +kernel

private def data_138_lower : Array (List Chunk) := #[
  [⟨1, 105, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨106, 113, ⟨0, 3, false, true, false, 106, 106⟩⟩,
   ⟨114, 247, ⟨3, 7, false, true, false, 114, 114⟩⟩],
  [⟨47, 105, ⟨0, 3, true, true, false, 105, 105⟩⟩,
   ⟨106, 137, ⟨0, 3, false, true, false, 137, 137⟩⟩,
   ⟨138, 269, ⟨3, 7, false, true, false, 138, 138⟩⟩,
   ⟨270, 271, ⟨3, 7, false, false, false, 270, 270⟩⟩],
  [⟨70, 105, ⟨0, 2, true, true, false, 105, 105⟩⟩,
   ⟨106, 137, ⟨0, 2, false, true, false, 137, 137⟩⟩,
   ⟨138, 269, ⟨2, 7, false, true, false, 138, 138⟩⟩,
   ⟨270, 294, ⟨2, 7, false, false, false, 270, 270⟩⟩],
  [⟨94, 105, ⟨0, 2, true, true, false, 105, 105⟩⟩,
   ⟨106, 160, ⟨0, 2, false, true, false, 160, 160⟩⟩,
   ⟨161, 269, ⟨2, 7, false, true, false, 269, 269⟩⟩,
   ⟨270, 340, ⟨2, 7, false, false, false, 340, 340⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_138_lower : ConfigurationBounds 138 1818 73 := by
  apply configuration_of_cells 138 1818 73 data_138_lower
  decide +kernel

private def data_139_lower : Array (List Chunk) := #[
  [⟨1, 106, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨107, 114, ⟨0, 3, false, true, false, 107, 107⟩⟩,
   ⟨115, 173, ⟨3, 7, false, true, false, 115, 115⟩⟩,
   ⟨174, 248, ⟨3, 7, false, false, false, 174, 174⟩⟩],
  [⟨48, 106, ⟨0, 3, true, true, false, 106, 106⟩⟩,
   ⟨107, 138, ⟨0, 3, false, true, false, 138, 138⟩⟩,
   ⟨139, 173, ⟨3, 7, false, true, false, 139, 139⟩⟩,
   ⟨174, 272, ⟨3, 7, false, false, false, 174, 174⟩⟩],
  [⟨71, 106, ⟨0, 2, true, true, false, 106, 106⟩⟩,
   ⟨107, 138, ⟨0, 2, false, true, false, 138, 138⟩⟩,
   ⟨139, 173, ⟨2, 7, false, true, false, 139, 139⟩⟩,
   ⟨174, 295, ⟨2, 7, false, false, false, 174, 174⟩⟩],
  [⟨95, 106, ⟨0, 2, true, true, false, 106, 106⟩⟩,
   ⟨107, 161, ⟨0, 2, false, true, false, 161, 161⟩⟩,
   ⟨162, 173, ⟨2, 7, false, true, false, 173, 173⟩⟩,
   ⟨174, 342, ⟨2, 7, false, false, false, 342, 342⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_139_lower : ConfigurationBounds 139 1843 74 := by
  apply configuration_of_cells 139 1843 74 data_139_lower
  decide +kernel

private def data_140_lower : Array (List Chunk) := #[
  [⟨1, 106, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨107, 115, ⟨0, 3, false, true, false, 107, 107⟩⟩,
   ⟨116, 251, ⟨3, 7, false, true, false, 116, 116⟩⟩],
  [⟨48, 106, ⟨0, 3, true, true, false, 106, 106⟩⟩,
   ⟨107, 139, ⟨0, 3, false, true, false, 139, 139⟩⟩,
   ⟨140, 271, ⟨3, 7, false, true, false, 140, 140⟩⟩,
   ⟨272, 275, ⟨3, 7, false, false, false, 272, 272⟩⟩],
  [⟨71, 106, ⟨0, 2, true, true, false, 106, 106⟩⟩,
   ⟨107, 139, ⟨0, 2, false, true, false, 139, 139⟩⟩,
   ⟨140, 271, ⟨2, 7, false, true, false, 140, 140⟩⟩,
   ⟨272, 298, ⟨2, 7, false, false, false, 272, 272⟩⟩],
  [⟨95, 106, ⟨0, 2, true, true, false, 106, 106⟩⟩,
   ⟨107, 162, ⟨0, 2, false, true, false, 162, 162⟩⟩,
   ⟨163, 271, ⟨2, 7, false, true, false, 271, 271⟩⟩,
   ⟨272, 345, ⟨2, 7, false, false, false, 345, 345⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_140_lower : ConfigurationBounds 140 1870 74 := by
  apply configuration_of_cells 140 1870 74 data_140_lower
  decide +kernel

private def data_141_lower : Array (List Chunk) := #[
  [⟨1, 107, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨108, 116, ⟨0, 3, false, true, false, 108, 108⟩⟩,
   ⟨117, 243, ⟨3, 7, false, true, false, 117, 117⟩⟩,
   ⟨244, 252, ⟨3, 7, false, false, false, 244, 244⟩⟩],
  [⟨48, 107, ⟨0, 3, true, true, false, 107, 107⟩⟩,
   ⟨108, 140, ⟨0, 3, false, true, false, 140, 140⟩⟩,
   ⟨141, 243, ⟨3, 7, false, true, false, 141, 141⟩⟩,
   ⟨244, 276, ⟨3, 7, false, false, false, 244, 244⟩⟩],
  [⟨72, 107, ⟨0, 2, true, true, false, 107, 107⟩⟩,
   ⟨108, 140, ⟨0, 2, false, true, false, 140, 140⟩⟩,
   ⟨141, 243, ⟨2, 7, false, true, false, 141, 141⟩⟩,
   ⟨244, 300, ⟨2, 7, false, false, false, 244, 244⟩⟩],
  [⟨96, 107, ⟨0, 2, true, true, false, 107, 107⟩⟩,
   ⟨108, 164, ⟨0, 2, false, true, false, 164, 164⟩⟩,
   ⟨165, 243, ⟨2, 7, false, true, false, 243, 243⟩⟩,
   ⟨244, 347, ⟨2, 7, false, false, false, 347, 347⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_141_lower : ConfigurationBounds 141 1896 75 := by
  apply configuration_of_cells 141 1896 75 data_141_lower
  decide +kernel

private def data_142_lower : Array (List Chunk) := #[
  [⟨1, 108, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨109, 116, ⟨0, 3, false, true, false, 109, 109⟩⟩,
   ⟨117, 195, ⟨3, 7, false, true, false, 117, 117⟩⟩,
   ⟨196, 252, ⟨3, 7, false, false, false, 196, 196⟩⟩],
  [⟨49, 108, ⟨0, 3, true, true, false, 108, 108⟩⟩,
   ⟨109, 141, ⟨0, 3, false, true, false, 141, 141⟩⟩,
   ⟨142, 195, ⟨3, 7, false, true, false, 142, 142⟩⟩,
   ⟨196, 277, ⟨3, 7, false, false, false, 196, 196⟩⟩],
  [⟨73, 108, ⟨0, 2, true, true, false, 108, 108⟩⟩,
   ⟨109, 141, ⟨0, 2, false, true, false, 141, 141⟩⟩,
   ⟨142, 195, ⟨2, 7, false, true, false, 142, 142⟩⟩,
   ⟨196, 301, ⟨2, 7, false, false, false, 196, 196⟩⟩],
  [⟨98, 108, ⟨0, 2, true, true, false, 108, 108⟩⟩,
   ⟨109, 165, ⟨0, 2, false, true, false, 165, 165⟩⟩,
   ⟨166, 195, ⟨2, 7, false, true, false, 195, 195⟩⟩,
   ⟨196, 349, ⟨2, 7, false, false, false, 349, 349⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_142_lower : ConfigurationBounds 142 1922 76 := by
  apply configuration_of_cells 142 1922 76 data_142_lower
  decide +kernel

private def data_143_lower : Array (List Chunk) := #[
  [⟨1, 109, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨110, 117, ⟨0, 3, false, true, false, 110, 110⟩⟩,
   ⟨118, 233, ⟨3, 7, false, true, false, 118, 118⟩⟩,
   ⟨234, 255, ⟨3, 7, false, false, false, 234, 234⟩⟩],
  [⟨49, 109, ⟨0, 3, true, true, false, 109, 109⟩⟩,
   ⟨110, 142, ⟨0, 3, false, true, false, 142, 142⟩⟩,
   ⟨143, 233, ⟨3, 7, false, true, false, 143, 143⟩⟩,
   ⟨234, 280, ⟨3, 7, false, false, false, 234, 234⟩⟩],
  [⟨73, 109, ⟨0, 2, true, true, false, 109, 109⟩⟩,
   ⟨110, 142, ⟨0, 2, false, true, false, 142, 142⟩⟩,
   ⟨143, 233, ⟨2, 7, false, true, false, 143, 143⟩⟩,
   ⟨234, 304, ⟨2, 7, false, false, false, 234, 234⟩⟩],
  [⟨98, 109, ⟨0, 2, true, true, false, 109, 109⟩⟩,
   ⟨110, 166, ⟨0, 2, false, true, false, 166, 166⟩⟩,
   ⟨167, 233, ⟨2, 7, false, true, false, 233, 233⟩⟩,
   ⟨234, 352, ⟨2, 7, false, false, false, 352, 352⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_143_lower : ConfigurationBounds 143 1949 76 := by
  apply configuration_of_cells 143 1949 76 data_143_lower
  decide +kernel

private def data_144_lower : Array (List Chunk) := #[
  [⟨1, 109, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨110, 118, ⟨0, 3, false, true, false, 110, 110⟩⟩,
   ⟨119, 253, ⟨3, 7, false, true, false, 119, 119⟩⟩,
   ⟨254, 258, ⟨3, 7, false, false, false, 254, 254⟩⟩],
  [⟨49, 109, ⟨0, 3, true, true, false, 109, 109⟩⟩,
   ⟨110, 143, ⟨0, 3, false, true, false, 143, 143⟩⟩,
   ⟨144, 253, ⟨3, 7, false, true, false, 144, 144⟩⟩,
   ⟨254, 283, ⟨3, 7, false, false, false, 254, 254⟩⟩],
  [⟨73, 109, ⟨0, 2, true, true, false, 109, 109⟩⟩,
   ⟨110, 143, ⟨0, 2, false, true, false, 143, 143⟩⟩,
   ⟨144, 253, ⟨2, 7, false, true, false, 144, 144⟩⟩,
   ⟨254, 307, ⟨2, 7, false, false, false, 254, 254⟩⟩],
  [⟨98, 109, ⟨0, 2, true, true, false, 109, 109⟩⟩,
   ⟨110, 167, ⟨0, 2, false, true, false, 167, 167⟩⟩,
   ⟨168, 253, ⟨2, 7, false, true, false, 253, 253⟩⟩,
   ⟨254, 355, ⟨2, 7, false, false, false, 355, 355⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_144_lower : ConfigurationBounds 144 1976 76 := by
  apply configuration_of_cells 144 1976 76 data_144_lower
  decide +kernel

private def data_145_lower : Array (List Chunk) := #[
  [⟨1, 110, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨111, 119, ⟨0, 3, false, true, false, 111, 111⟩⟩,
   ⟨120, 253, ⟨3, 7, false, true, false, 120, 120⟩⟩,
   ⟨254, 259, ⟨3, 7, false, false, false, 254, 254⟩⟩],
  [⟨50, 110, ⟨0, 3, true, true, false, 110, 110⟩⟩,
   ⟨111, 144, ⟨0, 3, false, true, false, 144, 144⟩⟩,
   ⟨145, 253, ⟨3, 7, false, true, false, 145, 145⟩⟩,
   ⟨254, 284, ⟨3, 7, false, false, false, 254, 254⟩⟩],
  [⟨74, 110, ⟨0, 2, true, true, false, 110, 110⟩⟩,
   ⟨111, 144, ⟨0, 2, false, true, false, 144, 144⟩⟩,
   ⟨145, 253, ⟨2, 7, false, true, false, 145, 145⟩⟩,
   ⟨254, 308, ⟨2, 7, false, false, false, 254, 254⟩⟩],
  [⟨99, 110, ⟨0, 2, true, true, false, 110, 110⟩⟩,
   ⟨111, 168, ⟨0, 2, false, true, false, 168, 168⟩⟩,
   ⟨169, 253, ⟨2, 7, false, true, false, 253, 253⟩⟩,
   ⟨254, 357, ⟨2, 7, false, false, false, 357, 357⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_145_lower : ConfigurationBounds 145 2003 77 := by
  apply configuration_of_cells 145 2003 77 data_145_lower
  decide +kernel

private def data_146_lower : Array (List Chunk) := #[
  [⟨1, 111, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨112, 120, ⟨0, 3, false, true, false, 112, 112⟩⟩,
   ⟨121, 234, ⟨3, 7, false, true, false, 121, 121⟩⟩,
   ⟨235, 260, ⟨3, 7, false, false, false, 235, 235⟩⟩],
  [⟨50, 111, ⟨0, 3, true, true, false, 111, 111⟩⟩,
   ⟨112, 145, ⟨0, 3, false, true, false, 145, 145⟩⟩,
   ⟨146, 234, ⟨3, 7, false, true, false, 146, 146⟩⟩,
   ⟨235, 285, ⟨3, 7, false, false, false, 235, 235⟩⟩],
  [⟨75, 111, ⟨0, 2, true, true, false, 111, 111⟩⟩,
   ⟨112, 145, ⟨0, 2, false, true, false, 145, 145⟩⟩,
   ⟨146, 234, ⟨2, 7, false, true, false, 146, 146⟩⟩,
   ⟨235, 310, ⟨2, 7, false, false, false, 235, 235⟩⟩],
  [⟨100, 111, ⟨0, 2, true, true, false, 111, 111⟩⟩,
   ⟨112, 170, ⟨0, 2, false, true, false, 170, 170⟩⟩,
   ⟨171, 234, ⟨2, 7, false, true, false, 234, 234⟩⟩,
   ⟨235, 359, ⟨2, 7, false, false, false, 359, 359⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_146_lower : ConfigurationBounds 146 2030 78 := by
  apply configuration_of_cells 146 2030 78 data_146_lower
  decide +kernel

private def data_147_lower : Array (List Chunk) := #[
  [⟨1, 112, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨113, 120, ⟨0, 3, false, true, false, 113, 113⟩⟩,
   ⟨121, 193, ⟨3, 7, false, true, false, 121, 121⟩⟩,
   ⟨194, 260, ⟨3, 7, false, false, false, 194, 194⟩⟩],
  [⟨51, 112, ⟨0, 3, true, true, false, 112, 112⟩⟩,
   ⟨113, 146, ⟨0, 3, false, true, false, 146, 146⟩⟩,
   ⟨147, 193, ⟨3, 7, false, true, false, 147, 147⟩⟩,
   ⟨194, 286, ⟨3, 7, false, false, false, 194, 194⟩⟩],
  [⟨76, 112, ⟨0, 2, true, true, false, 112, 112⟩⟩,
   ⟨113, 146, ⟨0, 2, false, true, false, 146, 146⟩⟩,
   ⟨147, 193, ⟨2, 7, false, true, false, 147, 147⟩⟩,
   ⟨194, 311, ⟨2, 7, false, false, false, 194, 194⟩⟩],
  [⟨102, 112, ⟨0, 2, true, true, false, 112, 112⟩⟩,
   ⟨113, 171, ⟨0, 2, false, true, false, 171, 171⟩⟩,
   ⟨172, 193, ⟨2, 7, false, true, false, 193, 193⟩⟩,
   ⟨194, 361, ⟨2, 7, false, false, false, 361, 361⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_147_lower : ConfigurationBounds 147 2057 79 := by
  apply configuration_of_cells 147 2057 79 data_147_lower
  decide +kernel

private def data_148_lower : Array (List Chunk) := #[
  [⟨1, 113, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨114, 121, ⟨0, 3, false, true, false, 114, 114⟩⟩,
   ⟨122, 242, ⟨3, 7, false, true, false, 122, 122⟩⟩,
   ⟨243, 263, ⟨3, 7, false, false, false, 243, 243⟩⟩],
  [⟨51, 113, ⟨0, 3, true, true, false, 113, 113⟩⟩,
   ⟨114, 147, ⟨0, 3, false, true, false, 147, 147⟩⟩,
   ⟨148, 242, ⟨3, 7, false, true, false, 148, 148⟩⟩,
   ⟨243, 289, ⟨3, 7, false, false, false, 243, 243⟩⟩],
  [⟨76, 113, ⟨0, 2, true, true, false, 113, 113⟩⟩,
   ⟨114, 147, ⟨0, 2, false, true, false, 147, 147⟩⟩,
   ⟨148, 242, ⟨2, 7, false, true, false, 148, 148⟩⟩,
   ⟨243, 314, ⟨2, 7, false, false, false, 243, 243⟩⟩],
  [⟨102, 113, ⟨0, 2, true, true, false, 113, 113⟩⟩,
   ⟨114, 172, ⟨0, 2, false, true, false, 172, 172⟩⟩,
   ⟨173, 242, ⟨2, 7, false, true, false, 242, 242⟩⟩,
   ⟨243, 364, ⟨2, 7, false, false, false, 364, 364⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_148_lower : ConfigurationBounds 148 2085 79 := by
  apply configuration_of_cells 148 2085 79 data_148_lower
  decide +kernel

private def data_149_lower : Array (List Chunk) := #[
  [⟨1, 113, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨114, 122, ⟨0, 3, false, true, false, 114, 114⟩⟩,
   ⟨123, 266, ⟨3, 7, false, true, false, 123, 123⟩⟩],
  [⟨51, 113, ⟨0, 3, true, true, false, 113, 113⟩⟩,
   ⟨114, 148, ⟨0, 3, false, true, false, 148, 148⟩⟩,
   ⟨149, 272, ⟨3, 7, false, true, false, 149, 149⟩⟩,
   ⟨273, 292, ⟨3, 7, false, false, false, 273, 273⟩⟩],
  [⟨76, 113, ⟨0, 2, true, true, false, 113, 113⟩⟩,
   ⟨114, 148, ⟨0, 2, false, true, false, 148, 148⟩⟩,
   ⟨149, 272, ⟨2, 7, false, true, false, 149, 149⟩⟩,
   ⟨273, 317, ⟨2, 7, false, false, false, 273, 273⟩⟩],
  [⟨102, 113, ⟨0, 2, true, true, false, 113, 113⟩⟩,
   ⟨114, 173, ⟨0, 2, false, true, false, 173, 173⟩⟩,
   ⟨174, 272, ⟨2, 7, false, true, false, 272, 272⟩⟩,
   ⟨273, 367, ⟨2, 7, false, false, false, 367, 367⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_149_lower : ConfigurationBounds 149 2113 79 := by
  apply configuration_of_cells 149 2113 79 data_149_lower
  decide +kernel

private def data_150_lower : Array (List Chunk) := #[
  [⟨1, 114, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨115, 123, ⟨0, 3, false, true, false, 115, 115⟩⟩,
   ⟨124, 267, ⟨3, 7, false, true, false, 124, 124⟩⟩],
  [⟨52, 114, ⟨0, 3, true, true, false, 114, 114⟩⟩,
   ⟨115, 149, ⟨0, 3, false, true, false, 149, 149⟩⟩,
   ⟨150, 282, ⟨3, 7, false, true, false, 150, 150⟩⟩,
   ⟨283, 293, ⟨3, 7, false, false, false, 283, 283⟩⟩],
  [⟨77, 114, ⟨0, 2, true, true, false, 114, 114⟩⟩,
   ⟨115, 149, ⟨0, 2, false, true, false, 149, 149⟩⟩,
   ⟨150, 282, ⟨2, 7, false, true, false, 150, 150⟩⟩,
   ⟨283, 318, ⟨2, 7, false, false, false, 283, 283⟩⟩],
  [⟨103, 114, ⟨0, 2, true, true, false, 114, 114⟩⟩,
   ⟨115, 174, ⟨0, 2, false, true, false, 174, 174⟩⟩,
   ⟨175, 282, ⟨2, 7, false, true, false, 282, 282⟩⟩,
   ⟨283, 369, ⟨2, 7, false, false, false, 369, 369⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_150_lower : ConfigurationBounds 150 2141 80 := by
  apply configuration_of_cells 150 2141 80 data_150_lower
  decide +kernel

private def data_151_lower : Array (List Chunk) := #[
  [⟨1, 115, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨116, 124, ⟨0, 3, false, true, false, 116, 116⟩⟩,
   ⟨125, 269, ⟨3, 7, false, true, false, 125, 125⟩⟩,
   ⟨270, 270, ⟨3, 7, false, false, false, 270, 270⟩⟩],
  [⟨52, 115, ⟨0, 3, true, true, false, 115, 115⟩⟩,
   ⟨116, 150, ⟨0, 3, false, true, false, 150, 150⟩⟩,
   ⟨151, 269, ⟨3, 7, false, true, false, 151, 151⟩⟩,
   ⟨270, 296, ⟨3, 7, false, false, false, 270, 270⟩⟩],
  [⟨77, 115, ⟨0, 2, true, true, false, 115, 115⟩⟩,
   ⟨116, 150, ⟨0, 2, false, true, false, 150, 150⟩⟩,
   ⟨151, 269, ⟨2, 7, false, true, false, 151, 151⟩⟩,
   ⟨270, 321, ⟨2, 7, false, false, false, 270, 270⟩⟩],
  [⟨103, 115, ⟨0, 2, true, true, false, 115, 115⟩⟩,
   ⟨116, 175, ⟨0, 2, false, true, false, 175, 175⟩⟩,
   ⟨176, 269, ⟨2, 7, false, true, false, 269, 269⟩⟩,
   ⟨270, 372, ⟨2, 7, false, false, false, 372, 372⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_151_lower : ConfigurationBounds 151 2169 80 := by
  apply configuration_of_cells 151 2169 80 data_151_lower
  decide +kernel

private def data_152_lower : Array (List Chunk) := #[
  [⟨1, 116, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨117, 125, ⟨0, 3, false, true, false, 117, 117⟩⟩,
   ⟨126, 237, ⟨3, 7, false, true, false, 126, 126⟩⟩,
   ⟨238, 271, ⟨3, 7, false, false, false, 238, 238⟩⟩],
  [⟨52, 116, ⟨0, 3, true, true, false, 116, 116⟩⟩,
   ⟨117, 151, ⟨0, 3, false, true, false, 151, 151⟩⟩,
   ⟨152, 237, ⟨3, 7, false, true, false, 152, 152⟩⟩,
   ⟨238, 297, ⟨3, 7, false, false, false, 238, 238⟩⟩],
  [⟨78, 116, ⟨0, 2, true, true, false, 116, 116⟩⟩,
   ⟨117, 151, ⟨0, 2, false, true, false, 151, 151⟩⟩,
   ⟨152, 237, ⟨2, 7, false, true, false, 152, 152⟩⟩,
   ⟨238, 323, ⟨2, 7, false, false, false, 238, 238⟩⟩],
  [⟨104, 116, ⟨0, 2, true, true, false, 116, 116⟩⟩,
   ⟨117, 177, ⟨0, 2, false, true, false, 177, 177⟩⟩,
   ⟨178, 237, ⟨2, 7, false, true, false, 237, 237⟩⟩,
   ⟨238, 374, ⟨2, 7, false, false, false, 374, 374⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_152_lower : ConfigurationBounds 152 2197 81 := by
  apply configuration_of_cells 152 2197 81 data_152_lower
  decide +kernel

private def data_153_lower : Array (List Chunk) := #[
  [⟨1, 116, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨117, 126, ⟨0, 3, false, true, false, 117, 117⟩⟩,
   ⟨127, 274, ⟨3, 7, false, true, false, 127, 127⟩⟩],
  [⟨52, 116, ⟨0, 3, true, true, false, 116, 116⟩⟩,
   ⟨117, 152, ⟨0, 3, false, true, false, 152, 152⟩⟩,
   ⟨153, 298, ⟨3, 7, false, true, false, 153, 153⟩⟩,
   ⟨299, 300, ⟨3, 7, false, false, false, 299, 299⟩⟩],
  [⟨78, 116, ⟨0, 2, true, true, false, 116, 116⟩⟩,
   ⟨117, 152, ⟨0, 2, false, true, false, 152, 152⟩⟩,
   ⟨153, 298, ⟨2, 7, false, true, false, 153, 153⟩⟩,
   ⟨299, 326, ⟨2, 7, false, false, false, 299, 299⟩⟩],
  [⟨104, 116, ⟨0, 2, true, true, false, 116, 116⟩⟩,
   ⟨117, 178, ⟨0, 2, false, true, false, 178, 178⟩⟩,
   ⟨179, 298, ⟨2, 7, false, true, false, 298, 298⟩⟩,
   ⟨299, 377, ⟨2, 7, false, false, false, 377, 377⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_153_lower : ConfigurationBounds 153 2226 81 := by
  apply configuration_of_cells 153 2226 81 data_153_lower
  decide +kernel

private def data_154_lower : Array (List Chunk) := #[
  [⟨1, 117, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨118, 126, ⟨0, 3, false, true, false, 118, 118⟩⟩,
   ⟨127, 222, ⟨3, 7, false, true, false, 127, 127⟩⟩,
   ⟨223, 274, ⟨3, 7, false, false, false, 223, 223⟩⟩],
  [⟨53, 117, ⟨0, 3, true, true, false, 117, 117⟩⟩,
   ⟨118, 153, ⟨0, 3, false, true, false, 153, 153⟩⟩,
   ⟨154, 222, ⟨3, 7, false, true, false, 154, 154⟩⟩,
   ⟨223, 301, ⟨3, 7, false, false, false, 223, 223⟩⟩],
  [⟨79, 117, ⟨0, 2, true, true, false, 117, 117⟩⟩,
   ⟨118, 153, ⟨0, 2, false, true, false, 153, 153⟩⟩,
   ⟨154, 222, ⟨2, 7, false, true, false, 154, 154⟩⟩,
   ⟨223, 327, ⟨2, 7, false, false, false, 223, 223⟩⟩],
  [⟨106, 117, ⟨0, 2, true, true, false, 117, 117⟩⟩,
   ⟨118, 179, ⟨0, 2, false, true, false, 179, 179⟩⟩,
   ⟨180, 222, ⟨2, 7, false, true, false, 222, 222⟩⟩,
   ⟨223, 379, ⟨2, 7, false, false, false, 379, 379⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_154_lower : ConfigurationBounds 154 2254 82 := by
  apply configuration_of_cells 154 2254 82 data_154_lower
  decide +kernel

private def data_155_lower : Array (List Chunk) := #[
  [⟨1, 118, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨119, 127, ⟨0, 3, false, true, false, 119, 119⟩⟩,
   ⟨128, 242, ⟨3, 7, false, true, false, 128, 128⟩⟩,
   ⟨243, 275, ⟨3, 7, false, false, false, 243, 243⟩⟩],
  [⟨54, 118, ⟨0, 3, true, true, false, 118, 118⟩⟩,
   ⟨119, 154, ⟨0, 3, false, true, false, 154, 154⟩⟩,
   ⟨155, 242, ⟨3, 7, false, true, false, 155, 155⟩⟩,
   ⟨243, 302, ⟨3, 7, false, false, false, 243, 243⟩⟩],
  [⟨80, 118, ⟨0, 2, true, true, false, 118, 118⟩⟩,
   ⟨119, 154, ⟨0, 2, false, true, false, 154, 154⟩⟩,
   ⟨155, 242, ⟨2, 7, false, true, false, 155, 155⟩⟩,
   ⟨243, 328, ⟨2, 7, false, false, false, 243, 243⟩⟩],
  [⟨107, 118, ⟨0, 2, true, true, false, 118, 118⟩⟩,
   ⟨119, 180, ⟨0, 2, false, true, false, 180, 180⟩⟩,
   ⟨181, 242, ⟨2, 7, false, true, false, 242, 242⟩⟩,
   ⟨243, 381, ⟨2, 7, false, false, false, 381, 381⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_155_lower : ConfigurationBounds 155 2283 83 := by
  apply configuration_of_cells 155 2283 83 data_155_lower
  decide +kernel

private def data_156_lower : Array (List Chunk) := #[
  [⟨1, 119, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨120, 128, ⟨0, 3, false, true, false, 120, 120⟩⟩,
   ⟨129, 238, ⟨3, 7, false, true, false, 129, 129⟩⟩,
   ⟨239, 278, ⟨3, 7, false, false, false, 239, 239⟩⟩],
  [⟨54, 119, ⟨0, 3, true, true, false, 119, 119⟩⟩,
   ⟨120, 155, ⟨0, 3, false, true, false, 155, 155⟩⟩,
   ⟨156, 238, ⟨3, 7, false, true, false, 156, 156⟩⟩,
   ⟨239, 305, ⟨3, 7, false, false, false, 239, 239⟩⟩],
  [⟨80, 119, ⟨0, 2, true, true, false, 119, 119⟩⟩,
   ⟨120, 155, ⟨0, 2, false, true, false, 155, 155⟩⟩,
   ⟨156, 238, ⟨2, 7, false, true, false, 156, 156⟩⟩,
   ⟨239, 331, ⟨2, 7, false, false, false, 239, 239⟩⟩],
  [⟨107, 119, ⟨0, 2, true, true, false, 119, 119⟩⟩,
   ⟨120, 181, ⟨0, 2, false, true, false, 181, 181⟩⟩,
   ⟨182, 238, ⟨2, 7, false, true, false, 238, 238⟩⟩,
   ⟨239, 384, ⟨2, 7, false, false, false, 384, 384⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_156_lower : ConfigurationBounds 156 2312 83 := by
  apply configuration_of_cells 156 2312 83 data_156_lower
  decide +kernel

private def data_157_lower : Array (List Chunk) := #[
  [⟨1, 120, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨121, 129, ⟨0, 3, false, true, false, 121, 121⟩⟩,
   ⟨130, 214, ⟨3, 7, false, true, false, 130, 130⟩⟩,
   ⟨215, 279, ⟨3, 7, false, false, false, 215, 215⟩⟩],
  [⟨54, 120, ⟨0, 3, true, true, false, 120, 120⟩⟩,
   ⟨121, 156, ⟨0, 3, false, true, false, 156, 156⟩⟩,
   ⟨157, 214, ⟨3, 7, false, true, false, 157, 157⟩⟩,
   ⟨215, 306, ⟨3, 7, false, false, false, 215, 215⟩⟩],
  [⟨81, 120, ⟨0, 2, true, true, false, 120, 120⟩⟩,
   ⟨121, 156, ⟨0, 2, false, true, false, 156, 156⟩⟩,
   ⟨157, 214, ⟨2, 7, false, true, false, 157, 157⟩⟩,
   ⟨215, 333, ⟨2, 7, false, false, false, 215, 215⟩⟩],
  [⟨108, 120, ⟨0, 2, true, true, false, 120, 120⟩⟩,
   ⟨121, 183, ⟨0, 2, false, true, false, 183, 183⟩⟩,
   ⟨184, 214, ⟨2, 7, false, true, false, 214, 214⟩⟩,
   ⟨215, 386, ⟨2, 7, false, false, false, 386, 386⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_157_lower : ConfigurationBounds 157 2341 84 := by
  apply configuration_of_cells 157 2341 84 data_157_lower
  decide +kernel

private def data_158_lower : Array (List Chunk) := #[
  [⟨1, 120, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨121, 130, ⟨0, 3, false, true, false, 121, 121⟩⟩,
   ⟨131, 282, ⟨3, 7, false, true, false, 131, 131⟩⟩],
  [⟨54, 120, ⟨0, 3, true, true, false, 120, 120⟩⟩,
   ⟨121, 157, ⟨0, 3, false, true, false, 157, 157⟩⟩,
   ⟨158, 287, ⟨3, 7, false, true, false, 158, 158⟩⟩,
   ⟨288, 309, ⟨3, 7, false, false, false, 288, 288⟩⟩],
  [⟨81, 120, ⟨0, 2, true, true, false, 120, 120⟩⟩,
   ⟨121, 157, ⟨0, 2, false, true, false, 157, 157⟩⟩,
   ⟨158, 287, ⟨2, 7, false, true, false, 158, 158⟩⟩,
   ⟨288, 336, ⟨2, 7, false, false, false, 288, 288⟩⟩],
  [⟨108, 120, ⟨0, 2, true, true, false, 120, 120⟩⟩,
   ⟨121, 184, ⟨0, 2, false, true, false, 184, 184⟩⟩,
   ⟨185, 287, ⟨2, 7, false, true, false, 287, 287⟩⟩,
   ⟨288, 389, ⟨2, 7, false, false, false, 389, 389⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_158_lower : ConfigurationBounds 158 2371 84 := by
  apply configuration_of_cells 158 2371 84 data_158_lower
  decide +kernel

private def data_159_lower : Array (List Chunk) := #[
  [⟨1, 121, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨122, 130, ⟨0, 3, false, true, false, 122, 122⟩⟩,
   ⟨131, 219, ⟨3, 7, false, true, false, 131, 131⟩⟩,
   ⟨220, 282, ⟨3, 7, false, false, false, 220, 220⟩⟩],
  [⟨55, 121, ⟨0, 3, true, true, false, 121, 121⟩⟩,
   ⟨122, 158, ⟨0, 3, false, true, false, 158, 158⟩⟩,
   ⟨159, 219, ⟨3, 7, false, true, false, 159, 159⟩⟩,
   ⟨220, 310, ⟨3, 7, false, false, false, 220, 220⟩⟩],
  [⟨82, 121, ⟨0, 2, true, true, false, 121, 121⟩⟩,
   ⟨122, 158, ⟨0, 2, false, true, false, 158, 158⟩⟩,
   ⟨159, 219, ⟨2, 7, false, true, false, 159, 159⟩⟩,
   ⟨220, 337, ⟨2, 7, false, false, false, 220, 220⟩⟩],
  [⟨110, 121, ⟨0, 2, true, true, false, 121, 121⟩⟩,
   ⟨122, 185, ⟨0, 2, false, true, false, 185, 185⟩⟩,
   ⟨186, 219, ⟨2, 7, false, true, false, 219, 219⟩⟩,
   ⟨220, 391, ⟨2, 7, false, false, false, 391, 391⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_159_lower : ConfigurationBounds 159 2400 85 := by
  apply configuration_of_cells 159 2400 85 data_159_lower
  decide +kernel

private def data_160_lower : Array (List Chunk) := #[
  [⟨1, 122, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨123, 131, ⟨0, 3, false, true, false, 123, 123⟩⟩,
   ⟨132, 247, ⟨3, 7, false, true, false, 132, 132⟩⟩,
   ⟨248, 285, ⟨3, 7, false, false, false, 248, 248⟩⟩],
  [⟨55, 122, ⟨0, 3, true, true, false, 122, 122⟩⟩,
   ⟨123, 159, ⟨0, 3, false, true, false, 159, 159⟩⟩,
   ⟨160, 247, ⟨3, 7, false, true, false, 160, 160⟩⟩,
   ⟨248, 313, ⟨3, 7, false, false, false, 248, 248⟩⟩],
  [⟨82, 122, ⟨0, 2, true, true, false, 122, 122⟩⟩,
   ⟨123, 159, ⟨0, 2, false, true, false, 159, 159⟩⟩,
   ⟨160, 247, ⟨2, 7, false, true, false, 160, 160⟩⟩,
   ⟨248, 340, ⟨2, 7, false, false, false, 248, 248⟩⟩],
  [⟨110, 122, ⟨0, 2, true, true, false, 122, 122⟩⟩,
   ⟨123, 186, ⟨0, 2, false, true, false, 186, 186⟩⟩,
   ⟨187, 247, ⟨2, 7, false, true, false, 247, 247⟩⟩,
   ⟨248, 394, ⟨2, 7, false, false, false, 394, 394⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_160_lower : ConfigurationBounds 160 2430 85 := by
  apply configuration_of_cells 160 2430 85 data_160_lower
  decide +kernel

private def data_161_lower : Array (List Chunk) := #[
  [⟨1, 123, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨124, 132, ⟨0, 3, false, true, false, 124, 124⟩⟩,
   ⟨133, 255, ⟨3, 7, false, true, false, 133, 133⟩⟩,
   ⟨256, 286, ⟨3, 7, false, false, false, 256, 256⟩⟩],
  [⟨56, 123, ⟨0, 3, true, true, false, 123, 123⟩⟩,
   ⟨124, 160, ⟨0, 3, false, true, false, 160, 160⟩⟩,
   ⟨161, 255, ⟨3, 7, false, true, false, 161, 161⟩⟩,
   ⟨256, 314, ⟨3, 7, false, false, false, 256, 256⟩⟩],
  [⟨83, 123, ⟨0, 2, true, true, false, 123, 123⟩⟩,
   ⟨124, 160, ⟨0, 2, false, true, false, 160, 160⟩⟩,
   ⟨161, 255, ⟨2, 7, false, true, false, 161, 161⟩⟩,
   ⟨256, 341, ⟨2, 7, false, false, false, 256, 256⟩⟩],
  [⟨111, 123, ⟨0, 2, true, true, false, 123, 123⟩⟩,
   ⟨124, 187, ⟨0, 2, false, true, false, 187, 187⟩⟩,
   ⟨188, 255, ⟨2, 7, false, true, false, 255, 255⟩⟩,
   ⟨256, 396, ⟨2, 7, false, false, false, 396, 396⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_161_lower : ConfigurationBounds 161 2460 86 := by
  apply configuration_of_cells 161 2460 86 data_161_lower
  decide +kernel

private def data_162_lower : Array (List Chunk) := #[
  [⟨1, 124, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨125, 133, ⟨0, 3, false, true, false, 125, 125⟩⟩,
   ⟨134, 241, ⟨3, 7, false, true, false, 134, 134⟩⟩,
   ⟨242, 287, ⟨3, 7, false, false, false, 242, 242⟩⟩],
  [⟨56, 124, ⟨0, 3, true, true, false, 124, 124⟩⟩,
   ⟨125, 161, ⟨0, 3, false, true, false, 161, 161⟩⟩,
   ⟨162, 241, ⟨3, 7, false, true, false, 162, 162⟩⟩,
   ⟨242, 315, ⟨3, 7, false, false, false, 242, 242⟩⟩],
  [⟨84, 124, ⟨0, 2, true, true, false, 124, 124⟩⟩,
   ⟨125, 161, ⟨0, 2, false, true, false, 161, 161⟩⟩,
   ⟨162, 241, ⟨2, 7, false, true, false, 162, 162⟩⟩,
   ⟨242, 343, ⟨2, 7, false, false, false, 242, 242⟩⟩],
  [⟨112, 124, ⟨0, 2, true, true, false, 124, 124⟩⟩,
   ⟨125, 189, ⟨0, 2, false, true, false, 189, 189⟩⟩,
   ⟨190, 241, ⟨2, 7, false, true, false, 241, 241⟩⟩,
   ⟨242, 398, ⟨2, 7, false, false, false, 398, 398⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_162_lower : ConfigurationBounds 162 2490 87 := by
  apply configuration_of_cells 162 2490 87 data_162_lower
  decide +kernel

private def data_163_lower : Array (List Chunk) := #[
  [⟨1, 125, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨126, 133, ⟨0, 3, false, true, false, 126, 126⟩⟩,
   ⟨134, 204, ⟨3, 7, false, true, false, 134, 134⟩⟩,
   ⟨205, 287, ⟨3, 7, false, false, false, 205, 205⟩⟩],
  [⟨57, 125, ⟨0, 3, true, true, false, 125, 125⟩⟩,
   ⟨126, 162, ⟨0, 3, false, true, false, 162, 162⟩⟩,
   ⟨163, 204, ⟨3, 7, false, true, false, 163, 163⟩⟩,
   ⟨205, 316, ⟨3, 7, false, false, false, 205, 205⟩⟩],
  [⟨85, 125, ⟨0, 2, true, true, false, 125, 125⟩⟩,
   ⟨126, 162, ⟨0, 2, false, true, false, 162, 162⟩⟩,
   ⟨163, 204, ⟨2, 7, false, true, false, 163, 163⟩⟩,
   ⟨205, 344, ⟨2, 7, false, false, false, 205, 205⟩⟩],
  [⟨114, 125, ⟨0, 2, true, true, false, 125, 125⟩⟩,
   ⟨126, 190, ⟨0, 2, false, true, false, 190, 190⟩⟩,
   ⟨191, 204, ⟨2, 7, false, true, false, 204, 204⟩⟩,
   ⟨205, 400, ⟨2, 7, false, false, false, 400, 400⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_163_lower : ConfigurationBounds 163 2520 88 := by
  apply configuration_of_cells 163 2520 88 data_163_lower
  decide +kernel

private def data_164_lower : Array (List Chunk) := #[
  [⟨1, 125, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨126, 134, ⟨0, 3, false, true, false, 126, 126⟩⟩,
   ⟨135, 266, ⟨3, 7, false, true, false, 135, 135⟩⟩,
   ⟨267, 290, ⟨3, 7, false, false, false, 267, 267⟩⟩],
  [⟨57, 125, ⟨0, 3, true, true, false, 125, 125⟩⟩,
   ⟨126, 163, ⟨0, 3, false, true, false, 163, 163⟩⟩,
   ⟨164, 266, ⟨3, 7, false, true, false, 164, 164⟩⟩,
   ⟨267, 319, ⟨3, 7, false, false, false, 267, 267⟩⟩],
  [⟨85, 125, ⟨0, 2, true, true, false, 125, 125⟩⟩,
   ⟨126, 163, ⟨0, 2, false, true, false, 163, 163⟩⟩,
   ⟨164, 266, ⟨2, 7, false, true, false, 164, 164⟩⟩,
   ⟨267, 347, ⟨2, 7, false, false, false, 267, 267⟩⟩],
  [⟨114, 125, ⟨0, 2, true, true, false, 125, 125⟩⟩,
   ⟨126, 191, ⟨0, 2, false, true, false, 191, 191⟩⟩,
   ⟨192, 266, ⟨2, 7, false, true, false, 266, 266⟩⟩,
   ⟨267, 403, ⟨2, 7, false, false, false, 403, 403⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_164_lower : ConfigurationBounds 164 2551 88 := by
  apply configuration_of_cells 164 2551 88 data_164_lower
  decide +kernel

private def data_165_lower : Array (List Chunk) := #[
  [⟨1, 126, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨127, 135, ⟨0, 3, false, true, false, 127, 127⟩⟩,
   ⟨136, 293, ⟨3, 7, false, true, false, 136, 136⟩⟩],
  [⟨57, 126, ⟨0, 3, true, true, false, 126, 126⟩⟩,
   ⟨127, 164, ⟨0, 3, false, true, false, 164, 164⟩⟩,
   ⟨165, 307, ⟨3, 7, false, true, false, 165, 165⟩⟩,
   ⟨308, 322, ⟨3, 7, false, false, false, 308, 308⟩⟩],
  [⟨85, 126, ⟨0, 2, true, true, false, 126, 126⟩⟩,
   ⟨127, 164, ⟨0, 2, false, true, false, 164, 164⟩⟩,
   ⟨165, 307, ⟨2, 7, false, true, false, 165, 165⟩⟩,
   ⟨308, 350, ⟨2, 7, false, false, false, 308, 308⟩⟩],
  [⟨114, 126, ⟨0, 2, true, true, false, 126, 126⟩⟩,
   ⟨127, 192, ⟨0, 2, false, true, false, 192, 192⟩⟩,
   ⟨193, 307, ⟨2, 7, false, true, false, 307, 307⟩⟩,
   ⟨308, 406, ⟨2, 7, false, false, false, 406, 406⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_165_lower : ConfigurationBounds 165 2582 88 := by
  apply configuration_of_cells 165 2582 88 data_165_lower
  decide +kernel

private def data_166_lower : Array (List Chunk) := #[
  [⟨1, 126, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨127, 136, ⟨0, 3, false, true, false, 127, 127⟩⟩,
   ⟨137, 296, ⟨3, 7, false, true, false, 137, 137⟩⟩],
  [⟨57, 126, ⟨0, 3, true, true, false, 126, 126⟩⟩,
   ⟨127, 165, ⟨0, 3, false, true, false, 165, 165⟩⟩,
   ⟨166, 324, ⟨3, 7, false, true, false, 166, 166⟩⟩,
   ⟨325, 325, ⟨3, 7, false, false, false, 325, 325⟩⟩],
  [⟨85, 126, ⟨0, 2, true, true, false, 126, 126⟩⟩,
   ⟨127, 165, ⟨0, 2, false, true, false, 165, 165⟩⟩,
   ⟨166, 324, ⟨2, 7, false, true, false, 166, 166⟩⟩,
   ⟨325, 353, ⟨2, 7, false, false, false, 325, 325⟩⟩],
  [⟨114, 126, ⟨0, 2, true, true, false, 126, 126⟩⟩,
   ⟨127, 193, ⟨0, 2, false, true, false, 193, 193⟩⟩,
   ⟨194, 324, ⟨2, 7, false, true, false, 324, 324⟩⟩,
   ⟨325, 409, ⟨2, 7, false, false, false, 409, 409⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_166_lower : ConfigurationBounds 166 2613 88 := by
  apply configuration_of_cells 166 2613 88 data_166_lower
  decide +kernel

private def data_167_lower : Array (List Chunk) := #[
  [⟨1, 127, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨128, 137, ⟨0, 3, false, true, false, 128, 128⟩⟩,
   ⟨138, 297, ⟨3, 7, false, true, false, 138, 138⟩⟩],
  [⟨58, 127, ⟨0, 3, true, true, false, 127, 127⟩⟩,
   ⟨128, 166, ⟨0, 3, false, true, false, 166, 166⟩⟩,
   ⟨167, 320, ⟨3, 7, false, true, false, 167, 167⟩⟩,
   ⟨321, 326, ⟨3, 7, false, false, false, 321, 321⟩⟩],
  [⟨86, 127, ⟨0, 2, true, true, false, 127, 127⟩⟩,
   ⟨128, 166, ⟨0, 2, false, true, false, 166, 166⟩⟩,
   ⟨167, 320, ⟨2, 7, false, true, false, 167, 167⟩⟩,
   ⟨321, 354, ⟨2, 7, false, false, false, 321, 321⟩⟩],
  [⟨115, 127, ⟨0, 2, true, true, false, 127, 127⟩⟩,
   ⟨128, 194, ⟨0, 2, false, true, false, 194, 194⟩⟩,
   ⟨195, 320, ⟨2, 7, false, true, false, 320, 320⟩⟩,
   ⟨321, 411, ⟨2, 7, false, false, false, 411, 411⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_167_lower : ConfigurationBounds 167 2644 89 := by
  apply configuration_of_cells 167 2644 89 data_167_lower
  decide +kernel

private def data_168_lower : Array (List Chunk) := #[
  [⟨1, 128, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨129, 138, ⟨0, 3, false, true, false, 129, 129⟩⟩,
   ⟨139, 292, ⟨3, 7, false, true, false, 139, 139⟩⟩,
   ⟨293, 298, ⟨3, 7, false, false, false, 293, 293⟩⟩],
  [⟨58, 128, ⟨0, 3, true, true, false, 128, 128⟩⟩,
   ⟨129, 167, ⟨0, 3, false, true, false, 167, 167⟩⟩,
   ⟨168, 292, ⟨3, 7, false, true, false, 168, 168⟩⟩,
   ⟨293, 327, ⟨3, 7, false, false, false, 293, 293⟩⟩],
  [⟨87, 128, ⟨0, 2, true, true, false, 128, 128⟩⟩,
   ⟨129, 167, ⟨0, 2, false, true, false, 167, 167⟩⟩,
   ⟨168, 292, ⟨2, 7, false, true, false, 168, 168⟩⟩,
   ⟨293, 356, ⟨2, 7, false, false, false, 293, 293⟩⟩],
  [⟨116, 128, ⟨0, 2, true, true, false, 128, 128⟩⟩,
   ⟨129, 196, ⟨0, 2, false, true, false, 196, 196⟩⟩,
   ⟨197, 292, ⟨2, 7, false, true, false, 292, 292⟩⟩,
   ⟨293, 413, ⟨2, 7, false, false, false, 413, 413⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_168_lower : ConfigurationBounds 168 2675 90 := by
  apply configuration_of_cells 168 2675 90 data_168_lower
  decide +kernel

private def data_169_lower : Array (List Chunk) := #[
  [⟨1, 129, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨130, 138, ⟨0, 3, false, true, false, 130, 130⟩⟩,
   ⟨139, 241, ⟨3, 7, false, true, false, 139, 139⟩⟩,
   ⟨242, 298, ⟨3, 7, false, false, false, 242, 242⟩⟩],
  [⟨59, 129, ⟨0, 3, true, true, false, 129, 129⟩⟩,
   ⟨130, 168, ⟨0, 3, false, true, false, 168, 168⟩⟩,
   ⟨169, 241, ⟨3, 7, false, true, false, 169, 169⟩⟩,
   ⟨242, 328, ⟨3, 7, false, false, false, 242, 242⟩⟩],
  [⟨88, 129, ⟨0, 2, true, true, false, 129, 129⟩⟩,
   ⟨130, 168, ⟨0, 2, false, true, false, 168, 168⟩⟩,
   ⟨169, 241, ⟨2, 7, false, true, false, 169, 169⟩⟩,
   ⟨242, 357, ⟨2, 7, false, false, false, 242, 242⟩⟩],
  [⟨118, 129, ⟨0, 2, true, true, false, 129, 129⟩⟩,
   ⟨130, 197, ⟨0, 2, false, true, false, 197, 197⟩⟩,
   ⟨198, 241, ⟨2, 7, false, true, false, 241, 241⟩⟩,
   ⟨242, 415, ⟨2, 7, false, false, false, 415, 415⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_169_lower : ConfigurationBounds 169 2706 91 := by
  apply configuration_of_cells 169 2706 91 data_169_lower
  decide +kernel

private def data_170_lower : Array (List Chunk) := #[
  [⟨1, 130, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨131, 139, ⟨0, 3, false, true, false, 131, 131⟩⟩,
   ⟨140, 292, ⟨3, 7, false, true, false, 140, 140⟩⟩,
   ⟨293, 301, ⟨3, 7, false, false, false, 293, 293⟩⟩],
  [⟨59, 130, ⟨0, 3, true, true, false, 130, 130⟩⟩,
   ⟨131, 169, ⟨0, 3, false, true, false, 169, 169⟩⟩,
   ⟨170, 292, ⟨3, 7, false, true, false, 170, 170⟩⟩,
   ⟨293, 331, ⟨3, 7, false, false, false, 293, 293⟩⟩],
  [⟨88, 130, ⟨0, 2, true, true, false, 130, 130⟩⟩,
   ⟨131, 169, ⟨0, 2, false, true, false, 169, 169⟩⟩,
   ⟨170, 292, ⟨2, 7, false, true, false, 170, 170⟩⟩,
   ⟨293, 360, ⟨2, 7, false, false, false, 293, 293⟩⟩],
  [⟨118, 130, ⟨0, 2, true, true, false, 130, 130⟩⟩,
   ⟨131, 198, ⟨0, 2, false, true, false, 198, 198⟩⟩,
   ⟨199, 292, ⟨2, 7, false, true, false, 292, 292⟩⟩,
   ⟨293, 418, ⟨2, 7, false, false, false, 418, 418⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_170_lower : ConfigurationBounds 170 2738 91 := by
  apply configuration_of_cells 170 2738 91 data_170_lower
  decide +kernel

private def data_171_lower : Array (List Chunk) := #[
  [⟨1, 130, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨131, 140, ⟨0, 3, false, true, false, 131, 131⟩⟩,
   ⟨141, 304, ⟨3, 7, false, true, false, 141, 141⟩⟩],
  [⟨59, 130, ⟨0, 3, true, true, false, 130, 130⟩⟩,
   ⟨131, 170, ⟨0, 3, false, true, false, 170, 170⟩⟩,
   ⟨171, 321, ⟨3, 7, false, true, false, 171, 171⟩⟩,
   ⟨322, 334, ⟨3, 7, false, false, false, 322, 322⟩⟩],
  [⟨88, 130, ⟨0, 2, true, true, false, 130, 130⟩⟩,
   ⟨131, 170, ⟨0, 2, false, true, false, 170, 170⟩⟩,
   ⟨171, 321, ⟨2, 7, false, true, false, 171, 171⟩⟩,
   ⟨322, 363, ⟨2, 7, false, false, false, 322, 322⟩⟩],
  [⟨118, 130, ⟨0, 2, true, true, false, 130, 130⟩⟩,
   ⟨131, 199, ⟨0, 2, false, true, false, 199, 199⟩⟩,
   ⟨200, 321, ⟨2, 7, false, true, false, 321, 321⟩⟩,
   ⟨322, 421, ⟨2, 7, false, false, false, 421, 421⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_171_lower : ConfigurationBounds 171 2770 91 := by
  apply configuration_of_cells 171 2770 91 data_171_lower
  decide +kernel

private def data_172_lower : Array (List Chunk) := #[
  [⟨1, 131, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨132, 141, ⟨0, 3, false, true, false, 132, 132⟩⟩,
   ⟨142, 305, ⟨3, 7, false, true, false, 142, 142⟩⟩],
  [⟨60, 131, ⟨0, 3, true, true, false, 131, 131⟩⟩,
   ⟨132, 171, ⟨0, 3, false, true, false, 171, 171⟩⟩,
   ⟨172, 327, ⟨3, 7, false, true, false, 172, 172⟩⟩,
   ⟨328, 335, ⟨3, 7, false, false, false, 328, 328⟩⟩],
  [⟨89, 131, ⟨0, 2, true, true, false, 131, 131⟩⟩,
   ⟨132, 171, ⟨0, 2, false, true, false, 171, 171⟩⟩,
   ⟨172, 327, ⟨2, 7, false, true, false, 172, 172⟩⟩,
   ⟨328, 364, ⟨2, 7, false, false, false, 328, 328⟩⟩],
  [⟨119, 131, ⟨0, 2, true, true, false, 131, 131⟩⟩,
   ⟨132, 200, ⟨0, 2, false, true, false, 200, 200⟩⟩,
   ⟨201, 327, ⟨2, 7, false, true, false, 327, 327⟩⟩,
   ⟨328, 423, ⟨2, 7, false, false, false, 423, 423⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_172_lower : ConfigurationBounds 172 2802 92 := by
  apply configuration_of_cells 172 2802 92 data_172_lower
  decide +kernel

private def data_173_lower : Array (List Chunk) := #[
  [⟨1, 132, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨133, 142, ⟨0, 3, false, true, false, 133, 133⟩⟩,
   ⟨143, 308, ⟨3, 7, false, true, false, 143, 143⟩⟩],
  [⟨60, 132, ⟨0, 3, true, true, false, 132, 132⟩⟩,
   ⟨133, 172, ⟨0, 3, false, true, false, 172, 172⟩⟩,
   ⟨173, 308, ⟨3, 7, false, true, false, 173, 173⟩⟩,
   ⟨309, 338, ⟨3, 7, false, false, false, 309, 309⟩⟩],
  [⟨89, 132, ⟨0, 2, true, true, false, 132, 132⟩⟩,
   ⟨133, 172, ⟨0, 2, false, true, false, 172, 172⟩⟩,
   ⟨173, 308, ⟨2, 7, false, true, false, 173, 173⟩⟩,
   ⟨309, 367, ⟨2, 7, false, false, false, 309, 309⟩⟩],
  [⟨119, 132, ⟨0, 2, true, true, false, 132, 132⟩⟩,
   ⟨133, 201, ⟨0, 2, false, true, false, 201, 201⟩⟩,
   ⟨202, 308, ⟨2, 7, false, true, false, 308, 308⟩⟩,
   ⟨309, 426, ⟨2, 7, false, false, false, 426, 426⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_173_lower : ConfigurationBounds 173 2834 92 := by
  apply configuration_of_cells 173 2834 92 data_173_lower
  decide +kernel

private def data_174_lower : Array (List Chunk) := #[
  [⟨1, 133, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨134, 143, ⟨0, 3, false, true, false, 134, 134⟩⟩,
   ⟨144, 266, ⟨3, 7, false, true, false, 144, 144⟩⟩,
   ⟨267, 309, ⟨3, 7, false, false, false, 267, 267⟩⟩],
  [⟨60, 133, ⟨0, 3, true, true, false, 133, 133⟩⟩,
   ⟨134, 173, ⟨0, 3, false, true, false, 173, 173⟩⟩,
   ⟨174, 266, ⟨3, 7, false, true, false, 174, 174⟩⟩,
   ⟨267, 339, ⟨3, 7, false, false, false, 267, 267⟩⟩],
  [⟨90, 133, ⟨0, 2, true, true, false, 133, 133⟩⟩,
   ⟨134, 173, ⟨0, 2, false, true, false, 173, 173⟩⟩,
   ⟨174, 266, ⟨2, 7, false, true, false, 174, 174⟩⟩,
   ⟨267, 369, ⟨2, 7, false, false, false, 267, 267⟩⟩],
  [⟨120, 133, ⟨0, 2, true, true, false, 133, 133⟩⟩,
   ⟨134, 203, ⟨0, 2, false, true, false, 203, 203⟩⟩,
   ⟨204, 266, ⟨2, 7, false, true, false, 266, 266⟩⟩,
   ⟨267, 428, ⟨2, 7, false, false, false, 428, 428⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_174_lower : ConfigurationBounds 174 2866 93 := by
  apply configuration_of_cells 174 2866 93 data_174_lower
  decide +kernel

private def data_175_lower : Array (List Chunk) := #[
  [⟨1, 133, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨134, 144, ⟨0, 3, false, true, false, 134, 134⟩⟩,
   ⟨145, 312, ⟨3, 7, false, true, false, 145, 145⟩⟩],
  [⟨60, 133, ⟨0, 3, true, true, false, 133, 133⟩⟩,
   ⟨134, 174, ⟨0, 3, false, true, false, 174, 174⟩⟩,
   ⟨175, 331, ⟨3, 7, false, true, false, 175, 175⟩⟩,
   ⟨332, 342, ⟨3, 7, false, false, false, 332, 332⟩⟩],
  [⟨90, 133, ⟨0, 2, true, true, false, 133, 133⟩⟩,
   ⟨134, 174, ⟨0, 2, false, true, false, 174, 174⟩⟩,
   ⟨175, 331, ⟨2, 7, false, true, false, 175, 175⟩⟩,
   ⟨332, 372, ⟨2, 7, false, false, false, 332, 332⟩⟩],
  [⟨120, 133, ⟨0, 2, true, true, false, 133, 133⟩⟩,
   ⟨134, 204, ⟨0, 2, false, true, false, 204, 204⟩⟩,
   ⟨205, 331, ⟨2, 7, false, true, false, 331, 331⟩⟩,
   ⟨332, 431, ⟨2, 7, false, false, false, 431, 431⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_175_lower : ConfigurationBounds 175 2899 93 := by
  apply configuration_of_cells 175 2899 93 data_175_lower
  decide +kernel

private def data_176_lower : Array (List Chunk) := #[
  [⟨1, 135, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨136, 144, ⟨0, 3, false, true, false, 136, 136⟩⟩,
   ⟨145, 240, ⟨3, 7, false, true, false, 145, 145⟩⟩,
   ⟨241, 310, ⟨3, 7, false, false, false, 241, 241⟩⟩],
  [⟨62, 135, ⟨0, 3, true, true, false, 135, 135⟩⟩,
   ⟨136, 175, ⟨0, 3, false, true, false, 175, 175⟩⟩,
   ⟨176, 240, ⟨3, 7, false, true, false, 176, 176⟩⟩,
   ⟨241, 341, ⟨3, 7, false, false, false, 241, 241⟩⟩],
  [⟨92, 135, ⟨0, 2, true, true, false, 135, 135⟩⟩,
   ⟨136, 175, ⟨0, 2, false, true, false, 175, 175⟩⟩,
   ⟨176, 240, ⟨2, 7, false, true, false, 176, 176⟩⟩,
   ⟨241, 371, ⟨2, 7, false, false, false, 241, 241⟩⟩],
  [⟨123, 135, ⟨0, 2, true, true, false, 135, 135⟩⟩,
   ⟨136, 205, ⟨0, 2, false, true, false, 205, 205⟩⟩,
   ⟨206, 240, ⟨2, 7, false, true, false, 240, 240⟩⟩,
   ⟨241, 432, ⟨2, 7, false, false, false, 432, 432⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_176_lower : ConfigurationBounds 176 2931 95 := by
  apply configuration_of_cells 176 2931 95 data_176_lower
  decide +kernel

private def data_177_lower : Array (List Chunk) := #[
  [⟨1, 135, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨136, 145, ⟨0, 3, false, true, false, 136, 136⟩⟩,
   ⟨146, 256, ⟨3, 7, false, true, false, 146, 146⟩⟩,
   ⟨257, 313, ⟨3, 7, false, false, false, 257, 257⟩⟩],
  [⟨62, 135, ⟨0, 3, true, true, false, 135, 135⟩⟩,
   ⟨136, 176, ⟨0, 3, false, true, false, 176, 176⟩⟩,
   ⟨177, 256, ⟨3, 7, false, true, false, 177, 177⟩⟩,
   ⟨257, 344, ⟨3, 7, false, false, false, 257, 257⟩⟩],
  [⟨92, 135, ⟨0, 2, true, true, false, 135, 135⟩⟩,
   ⟨136, 176, ⟨0, 2, false, true, false, 176, 176⟩⟩,
   ⟨177, 256, ⟨2, 7, false, true, false, 177, 177⟩⟩,
   ⟨257, 374, ⟨2, 7, false, false, false, 257, 257⟩⟩],
  [⟨123, 135, ⟨0, 2, true, true, false, 135, 135⟩⟩,
   ⟨136, 206, ⟨0, 2, false, true, false, 206, 206⟩⟩,
   ⟨207, 256, ⟨2, 7, false, true, false, 256, 256⟩⟩,
   ⟨257, 435, ⟨2, 7, false, false, false, 435, 435⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_177_lower : ConfigurationBounds 177 2964 95 := by
  apply configuration_of_cells 177 2964 95 data_177_lower
  decide +kernel

private def data_178_lower : Array (List Chunk) := #[
  [⟨1, 136, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨137, 146, ⟨0, 3, false, true, false, 137, 137⟩⟩,
   ⟨147, 248, ⟨3, 7, false, true, false, 147, 147⟩⟩,
   ⟨249, 314, ⟨3, 7, false, false, false, 249, 249⟩⟩],
  [⟨62, 136, ⟨0, 3, true, true, false, 136, 136⟩⟩,
   ⟨137, 177, ⟨0, 3, false, true, false, 177, 177⟩⟩,
   ⟨178, 248, ⟨3, 7, false, true, false, 178, 178⟩⟩,
   ⟨249, 345, ⟨3, 7, false, false, false, 249, 249⟩⟩],
  [⟨93, 136, ⟨0, 2, true, true, false, 136, 136⟩⟩,
   ⟨137, 177, ⟨0, 2, false, true, false, 177, 177⟩⟩,
   ⟨178, 248, ⟨2, 7, false, true, false, 178, 178⟩⟩,
   ⟨249, 376, ⟨2, 7, false, false, false, 249, 249⟩⟩],
  [⟨124, 136, ⟨0, 2, true, true, false, 136, 136⟩⟩,
   ⟨137, 208, ⟨0, 2, false, true, false, 208, 208⟩⟩,
   ⟨209, 248, ⟨2, 7, false, true, false, 248, 248⟩⟩,
   ⟨249, 437, ⟨2, 7, false, false, false, 437, 437⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_178_lower : ConfigurationBounds 178 2997 96 := by
  apply configuration_of_cells 178 2997 96 data_178_lower
  decide +kernel

private def data_179_lower : Array (List Chunk) := #[
  [⟨1, 136, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨137, 147, ⟨0, 3, false, true, false, 137, 137⟩⟩,
   ⟨148, 319, ⟨3, 7, false, true, false, 148, 148⟩⟩],
  [⟨62, 136, ⟨0, 3, true, true, false, 136, 136⟩⟩,
   ⟨137, 178, ⟨0, 3, false, true, false, 178, 178⟩⟩,
   ⟨179, 349, ⟨3, 7, false, true, false, 179, 179⟩⟩,
   ⟨350, 350, ⟨3, 7, false, false, false, 350, 350⟩⟩],
  [⟨92, 136, ⟨0, 2, true, true, false, 136, 136⟩⟩,
   ⟨137, 178, ⟨0, 2, false, true, false, 178, 178⟩⟩,
   ⟨179, 349, ⟨2, 7, false, true, false, 179, 179⟩⟩,
   ⟨350, 380, ⟨2, 7, false, false, false, 350, 350⟩⟩],
  [⟨123, 136, ⟨0, 2, true, true, false, 136, 136⟩⟩,
   ⟨137, 208, ⟨0, 2, false, true, false, 208, 208⟩⟩,
   ⟨209, 349, ⟨2, 7, false, true, false, 349, 349⟩⟩,
   ⟨350, 441, ⟨2, 7, false, false, false, 441, 441⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_179_lower : ConfigurationBounds 179 3031 95 := by
  apply configuration_of_cells 179 3031 95 data_179_lower
  decide +kernel

private def data_180_lower : Array (List Chunk) := #[
  [⟨1, 137, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨138, 148, ⟨0, 3, false, true, false, 138, 138⟩⟩,
   ⟨149, 291, ⟨3, 7, false, true, false, 149, 149⟩⟩,
   ⟨292, 320, ⟨3, 7, false, false, false, 292, 292⟩⟩],
  [⟨62, 137, ⟨0, 3, true, true, false, 137, 137⟩⟩,
   ⟨138, 179, ⟨0, 3, false, true, false, 179, 179⟩⟩,
   ⟨180, 291, ⟨3, 7, false, true, false, 180, 180⟩⟩,
   ⟨292, 351, ⟨3, 7, false, false, false, 292, 292⟩⟩],
  [⟨93, 137, ⟨0, 2, true, true, false, 137, 137⟩⟩,
   ⟨138, 179, ⟨0, 2, false, true, false, 179, 179⟩⟩,
   ⟨180, 291, ⟨2, 7, false, true, false, 180, 180⟩⟩,
   ⟨292, 382, ⟨2, 7, false, false, false, 292, 292⟩⟩],
  [⟨124, 137, ⟨0, 2, true, true, false, 137, 137⟩⟩,
   ⟨138, 210, ⟨0, 2, false, true, false, 210, 210⟩⟩,
   ⟨211, 291, ⟨2, 7, false, true, false, 291, 291⟩⟩,
   ⟨292, 443, ⟨2, 7, false, false, false, 443, 443⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_180_lower : ConfigurationBounds 180 3064 96 := by
  apply configuration_of_cells 180 3064 96 data_180_lower
  decide +kernel

private def data_181_lower : Array (List Chunk) := #[
  [⟨1, 138, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨139, 148, ⟨0, 3, false, true, false, 139, 139⟩⟩,
   ⟨149, 320, ⟨3, 7, false, true, false, 149, 149⟩⟩],
  [⟨63, 138, ⟨0, 3, true, true, false, 138, 138⟩⟩,
   ⟨139, 180, ⟨0, 3, false, true, false, 180, 180⟩⟩,
   ⟨181, 345, ⟨3, 7, false, true, false, 181, 181⟩⟩,
   ⟨346, 352, ⟨3, 7, false, false, false, 346, 346⟩⟩],
  [⟨94, 138, ⟨0, 2, true, true, false, 138, 138⟩⟩,
   ⟨139, 180, ⟨0, 2, false, true, false, 180, 180⟩⟩,
   ⟨181, 345, ⟨2, 7, false, true, false, 181, 181⟩⟩,
   ⟨346, 383, ⟨2, 7, false, false, false, 346, 346⟩⟩],
  [⟨126, 138, ⟨0, 2, true, true, false, 138, 138⟩⟩,
   ⟨139, 211, ⟨0, 2, false, true, false, 211, 211⟩⟩,
   ⟨212, 345, ⟨2, 7, false, true, false, 345, 345⟩⟩,
   ⟨346, 445, ⟨2, 7, false, false, false, 445, 445⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_181_lower : ConfigurationBounds 181 3098 97 := by
  apply configuration_of_cells 181 3098 97 data_181_lower
  decide +kernel

private def data_182_lower : Array (List Chunk) := #[
  [⟨1, 139, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨140, 149, ⟨0, 3, false, true, false, 140, 140⟩⟩,
   ⟨150, 237, ⟨3, 7, false, true, false, 150, 150⟩⟩,
   ⟨238, 321, ⟨3, 7, false, false, false, 238, 238⟩⟩],
  [⟨64, 139, ⟨0, 3, true, true, false, 139, 139⟩⟩,
   ⟨140, 181, ⟨0, 3, false, true, false, 181, 181⟩⟩,
   ⟨182, 237, ⟨3, 7, false, true, false, 182, 182⟩⟩,
   ⟨238, 353, ⟨3, 7, false, false, false, 238, 238⟩⟩],
  [⟨95, 139, ⟨0, 2, true, true, false, 139, 139⟩⟩,
   ⟨140, 181, ⟨0, 2, false, true, false, 181, 181⟩⟩,
   ⟨182, 237, ⟨2, 7, false, true, false, 182, 182⟩⟩,
   ⟨238, 384, ⟨2, 7, false, false, false, 238, 238⟩⟩],
  [⟨127, 139, ⟨0, 2, true, true, false, 139, 139⟩⟩,
   ⟨140, 212, ⟨0, 2, false, true, false, 212, 212⟩⟩,
   ⟨213, 237, ⟨2, 7, false, true, false, 237, 237⟩⟩,
   ⟨238, 447, ⟨2, 7, false, false, false, 447, 447⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_182_lower : ConfigurationBounds 182 3131 98 := by
  apply configuration_of_cells 182 3131 98 data_182_lower
  decide +kernel

private def data_183_lower : Array (List Chunk) := #[
  [⟨1, 140, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨141, 150, ⟨0, 3, false, true, false, 141, 141⟩⟩,
   ⟨151, 238, ⟨3, 7, false, true, false, 151, 151⟩⟩,
   ⟨239, 324, ⟨3, 7, false, false, false, 239, 239⟩⟩],
  [⟨64, 140, ⟨0, 3, true, true, false, 140, 140⟩⟩,
   ⟨141, 182, ⟨0, 3, false, true, false, 182, 182⟩⟩,
   ⟨183, 238, ⟨3, 7, false, true, false, 183, 183⟩⟩,
   ⟨239, 356, ⟨3, 7, false, false, false, 239, 239⟩⟩],
  [⟨95, 140, ⟨0, 2, true, true, false, 140, 140⟩⟩,
   ⟨141, 182, ⟨0, 2, false, true, false, 182, 182⟩⟩,
   ⟨183, 238, ⟨2, 7, false, true, false, 183, 183⟩⟩,
   ⟨239, 387, ⟨2, 7, false, false, false, 239, 239⟩⟩],
  [⟨127, 140, ⟨0, 2, true, true, false, 140, 140⟩⟩,
   ⟨141, 213, ⟨0, 2, false, true, false, 213, 213⟩⟩,
   ⟨214, 238, ⟨2, 7, false, true, false, 238, 238⟩⟩,
   ⟨239, 450, ⟨2, 7, false, false, false, 450, 450⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_183_lower : ConfigurationBounds 183 3165 98 := by
  apply configuration_of_cells 183 3165 98 data_183_lower
  decide +kernel

private def data_184_lower : Array (List Chunk) := #[
  [⟨1, 140, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨141, 151, ⟨0, 3, false, true, false, 141, 141⟩⟩,
   ⟨152, 327, ⟨3, 7, false, true, false, 152, 152⟩⟩],
  [⟨64, 140, ⟨0, 3, true, true, false, 140, 140⟩⟩,
   ⟨141, 183, ⟨0, 3, false, true, false, 183, 183⟩⟩,
   ⟨184, 355, ⟨3, 7, false, true, false, 184, 184⟩⟩,
   ⟨356, 359, ⟨3, 7, false, false, false, 356, 356⟩⟩],
  [⟨95, 140, ⟨0, 2, true, true, false, 140, 140⟩⟩,
   ⟨141, 183, ⟨0, 2, false, true, false, 183, 183⟩⟩,
   ⟨184, 355, ⟨2, 7, false, true, false, 184, 184⟩⟩,
   ⟨356, 390, ⟨2, 7, false, false, false, 356, 356⟩⟩],
  [⟨127, 140, ⟨0, 2, true, true, false, 140, 140⟩⟩,
   ⟨141, 214, ⟨0, 2, false, true, false, 214, 214⟩⟩,
   ⟨215, 355, ⟨2, 7, false, true, false, 355, 355⟩⟩,
   ⟨356, 453, ⟨2, 7, false, false, false, 453, 453⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_184_lower : ConfigurationBounds 184 3200 98 := by
  apply configuration_of_cells 184 3200 98 data_184_lower
  decide +kernel

private def data_185_lower : Array (List Chunk) := #[
  [⟨1, 141, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨142, 152, ⟨0, 3, false, true, false, 142, 142⟩⟩,
   ⟨153, 307, ⟨3, 7, false, true, false, 153, 153⟩⟩,
   ⟨308, 328, ⟨3, 7, false, false, false, 308, 308⟩⟩],
  [⟨64, 141, ⟨0, 3, true, true, false, 141, 141⟩⟩,
   ⟨142, 184, ⟨0, 3, false, true, false, 184, 184⟩⟩,
   ⟨185, 307, ⟨3, 7, false, true, false, 185, 185⟩⟩,
   ⟨308, 360, ⟨3, 7, false, false, false, 308, 308⟩⟩],
  [⟨96, 141, ⟨0, 2, true, true, false, 141, 141⟩⟩,
   ⟨142, 184, ⟨0, 2, false, true, false, 184, 184⟩⟩,
   ⟨185, 307, ⟨2, 7, false, true, false, 185, 185⟩⟩,
   ⟨308, 392, ⟨2, 7, false, false, false, 308, 308⟩⟩],
  [⟨128, 141, ⟨0, 2, true, true, false, 141, 141⟩⟩,
   ⟨142, 216, ⟨0, 2, false, true, false, 216, 216⟩⟩,
   ⟨217, 307, ⟨2, 7, false, true, false, 307, 307⟩⟩,
   ⟨308, 455, ⟨2, 7, false, false, false, 455, 455⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_185_lower : ConfigurationBounds 185 3234 99 := by
  apply configuration_of_cells 185 3234 99 data_185_lower
  decide +kernel

private def data_186_lower : Array (List Chunk) := #[
  [⟨1, 142, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨143, 152, ⟨0, 3, false, true, false, 143, 143⟩⟩,
   ⟨153, 233, ⟨3, 7, false, true, false, 153, 153⟩⟩,
   ⟨234, 328, ⟨3, 7, false, false, false, 234, 234⟩⟩],
  [⟨65, 142, ⟨0, 3, true, true, false, 142, 142⟩⟩,
   ⟨143, 185, ⟨0, 3, false, true, false, 185, 185⟩⟩,
   ⟨186, 233, ⟨3, 7, false, true, false, 186, 186⟩⟩,
   ⟨234, 361, ⟨3, 7, false, false, false, 234, 234⟩⟩],
  [⟨97, 142, ⟨0, 2, true, true, false, 142, 142⟩⟩,
   ⟨143, 185, ⟨0, 2, false, true, false, 185, 185⟩⟩,
   ⟨186, 233, ⟨2, 7, false, true, false, 186, 186⟩⟩,
   ⟨234, 393, ⟨2, 7, false, false, false, 234, 234⟩⟩],
  [⟨130, 142, ⟨0, 2, true, true, false, 142, 142⟩⟩,
   ⟨143, 217, ⟨0, 2, false, true, false, 217, 217⟩⟩,
   ⟨218, 233, ⟨2, 7, false, true, false, 233, 233⟩⟩,
   ⟨234, 457, ⟨2, 7, false, false, false, 457, 457⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_186_lower : ConfigurationBounds 186 3268 100 := by
  apply configuration_of_cells 186 3268 100 data_186_lower
  decide +kernel

private def data_187_lower : Array (List Chunk) := #[
  [⟨1, 143, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨144, 153, ⟨0, 3, false, true, false, 144, 144⟩⟩,
   ⟨154, 273, ⟨3, 7, false, true, false, 154, 154⟩⟩,
   ⟨274, 331, ⟨3, 7, false, false, false, 274, 274⟩⟩],
  [⟨65, 143, ⟨0, 3, true, true, false, 143, 143⟩⟩,
   ⟨144, 186, ⟨0, 3, false, true, false, 186, 186⟩⟩,
   ⟨187, 273, ⟨3, 7, false, true, false, 187, 187⟩⟩,
   ⟨274, 364, ⟨3, 7, false, false, false, 274, 274⟩⟩],
  [⟨97, 143, ⟨0, 2, true, true, false, 143, 143⟩⟩,
   ⟨144, 186, ⟨0, 2, false, true, false, 186, 186⟩⟩,
   ⟨187, 273, ⟨2, 7, false, true, false, 187, 187⟩⟩,
   ⟨274, 396, ⟨2, 7, false, false, false, 274, 274⟩⟩],
  [⟨130, 143, ⟨0, 2, true, true, false, 143, 143⟩⟩,
   ⟨144, 218, ⟨0, 2, false, true, false, 218, 218⟩⟩,
   ⟨219, 273, ⟨2, 7, false, true, false, 273, 273⟩⟩,
   ⟨274, 460, ⟨2, 7, false, false, false, 460, 460⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_187_lower : ConfigurationBounds 187 3303 100 := by
  apply configuration_of_cells 187 3303 100 data_187_lower
  decide +kernel

private def data_188_lower : Array (List Chunk) := #[
  [⟨1, 144, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨145, 154, ⟨0, 3, false, true, false, 145, 145⟩⟩,
   ⟨155, 288, ⟨3, 7, false, true, false, 155, 155⟩⟩,
   ⟨289, 332, ⟨3, 7, false, false, false, 289, 289⟩⟩],
  [⟨66, 144, ⟨0, 3, true, true, false, 144, 144⟩⟩,
   ⟨145, 187, ⟨0, 3, false, true, false, 187, 187⟩⟩,
   ⟨188, 288, ⟨3, 7, false, true, false, 188, 188⟩⟩,
   ⟨289, 365, ⟨3, 7, false, false, false, 289, 289⟩⟩],
  [⟨98, 144, ⟨0, 2, true, true, false, 144, 144⟩⟩,
   ⟨145, 187, ⟨0, 2, false, true, false, 187, 187⟩⟩,
   ⟨188, 288, ⟨2, 7, false, true, false, 188, 188⟩⟩,
   ⟨289, 397, ⟨2, 7, false, false, false, 289, 289⟩⟩],
  [⟨131, 144, ⟨0, 2, true, true, false, 144, 144⟩⟩,
   ⟨145, 219, ⟨0, 2, false, true, false, 219, 219⟩⟩,
   ⟨220, 288, ⟨2, 7, false, true, false, 288, 288⟩⟩,
   ⟨289, 462, ⟨2, 7, false, false, false, 462, 462⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_188_lower : ConfigurationBounds 188 3338 101 := by
  apply configuration_of_cells 188 3338 101 data_188_lower
  decide +kernel

private def data_189_lower : Array (List Chunk) := #[
  [⟨1, 145, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨146, 155, ⟨0, 3, false, true, false, 146, 146⟩⟩,
   ⟨156, 278, ⟨3, 7, false, true, false, 156, 156⟩⟩,
   ⟨279, 333, ⟨3, 7, false, false, false, 279, 279⟩⟩],
  [⟨66, 145, ⟨0, 3, true, true, false, 145, 145⟩⟩,
   ⟨146, 188, ⟨0, 3, false, true, false, 188, 188⟩⟩,
   ⟨189, 278, ⟨3, 7, false, true, false, 189, 189⟩⟩,
   ⟨279, 366, ⟨3, 7, false, false, false, 279, 279⟩⟩],
  [⟨99, 145, ⟨0, 2, true, true, false, 145, 145⟩⟩,
   ⟨146, 188, ⟨0, 2, false, true, false, 188, 188⟩⟩,
   ⟨189, 278, ⟨2, 7, false, true, false, 189, 189⟩⟩,
   ⟨279, 399, ⟨2, 7, false, false, false, 279, 279⟩⟩],
  [⟨132, 145, ⟨0, 2, true, true, false, 145, 145⟩⟩,
   ⟨146, 221, ⟨0, 2, false, true, false, 221, 221⟩⟩,
   ⟨222, 278, ⟨2, 7, false, true, false, 278, 278⟩⟩,
   ⟨279, 464, ⟨2, 7, false, false, false, 464, 464⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_189_lower : ConfigurationBounds 189 3373 102 := by
  apply configuration_of_cells 189 3373 102 data_189_lower
  decide +kernel

private def data_190_lower : Array (List Chunk) := #[
  [⟨1, 145, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨146, 156, ⟨0, 3, false, true, false, 146, 146⟩⟩,
   ⟨157, 239, ⟨3, 7, false, true, false, 157, 157⟩⟩,
   ⟨240, 336, ⟨3, 7, false, false, false, 240, 240⟩⟩],
  [⟨66, 145, ⟨0, 3, true, true, false, 145, 145⟩⟩,
   ⟨146, 189, ⟨0, 3, false, true, false, 189, 189⟩⟩,
   ⟨190, 239, ⟨3, 7, false, true, false, 190, 190⟩⟩,
   ⟨240, 369, ⟨3, 7, false, false, false, 240, 240⟩⟩],
  [⟨99, 145, ⟨0, 2, true, true, false, 145, 145⟩⟩,
   ⟨146, 189, ⟨0, 2, false, true, false, 189, 189⟩⟩,
   ⟨190, 239, ⟨2, 7, false, true, false, 190, 190⟩⟩,
   ⟨240, 402, ⟨2, 7, false, false, false, 240, 240⟩⟩],
  [⟨132, 145, ⟨0, 2, true, true, false, 145, 145⟩⟩,
   ⟨146, 222, ⟨0, 2, false, true, false, 222, 222⟩⟩,
   ⟨223, 239, ⟨2, 7, false, true, false, 239, 239⟩⟩,
   ⟨240, 467, ⟨2, 7, false, false, false, 467, 467⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_190_lower : ConfigurationBounds 190 3408 102 := by
  apply configuration_of_cells 190 3408 102 data_190_lower
  decide +kernel

private def data_191_lower : Array (List Chunk) := #[
  [⟨1, 146, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨147, 157, ⟨0, 3, false, true, false, 147, 147⟩⟩,
   ⟨158, 318, ⟨3, 7, false, true, false, 158, 158⟩⟩,
   ⟨319, 339, ⟨3, 7, false, false, false, 319, 319⟩⟩],
  [⟨66, 146, ⟨0, 3, true, true, false, 146, 146⟩⟩,
   ⟨147, 190, ⟨0, 3, false, true, false, 190, 190⟩⟩,
   ⟨191, 318, ⟨3, 7, false, true, false, 191, 191⟩⟩,
   ⟨319, 372, ⟨3, 7, false, false, false, 319, 319⟩⟩],
  [⟨99, 146, ⟨0, 2, true, true, false, 146, 146⟩⟩,
   ⟨147, 190, ⟨0, 2, false, true, false, 190, 190⟩⟩,
   ⟨191, 318, ⟨2, 7, false, true, false, 191, 191⟩⟩,
   ⟨319, 405, ⟨2, 7, false, false, false, 319, 319⟩⟩],
  [⟨132, 146, ⟨0, 2, true, true, false, 146, 146⟩⟩,
   ⟨147, 223, ⟨0, 2, false, true, false, 223, 223⟩⟩,
   ⟨224, 318, ⟨2, 7, false, true, false, 318, 318⟩⟩,
   ⟨319, 470, ⟨2, 7, false, false, false, 470, 470⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_191_lower : ConfigurationBounds 191 3444 102 := by
  apply configuration_of_cells 191 3444 102 data_191_lower
  decide +kernel

private def data_192_lower : Array (List Chunk) := #[
  [⟨1, 147, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨148, 157, ⟨0, 3, false, true, false, 148, 148⟩⟩,
   ⟨158, 339, ⟨3, 7, false, true, false, 158, 158⟩⟩],
  [⟨67, 147, ⟨0, 3, true, true, false, 147, 147⟩⟩,
   ⟨148, 191, ⟨0, 3, false, true, false, 191, 191⟩⟩,
   ⟨192, 373, ⟨3, 7, false, true, false, 192, 192⟩⟩],
  [⟨100, 147, ⟨0, 2, true, true, false, 147, 147⟩⟩,
   ⟨148, 191, ⟨0, 2, false, true, false, 191, 191⟩⟩,
   ⟨192, 373, ⟨2, 7, false, true, false, 192, 192⟩⟩,
   ⟨374, 406, ⟨2, 7, false, false, false, 374, 374⟩⟩],
  [⟨134, 147, ⟨0, 2, true, true, false, 147, 147⟩⟩,
   ⟨148, 224, ⟨0, 2, false, true, false, 224, 224⟩⟩,
   ⟨225, 373, ⟨2, 7, false, true, false, 373, 373⟩⟩,
   ⟨374, 472, ⟨2, 7, false, false, false, 472, 472⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_192_lower : ConfigurationBounds 192 3480 103 := by
  apply configuration_of_cells 192 3480 103 data_192_lower
  decide +kernel

private def data_193_lower : Array (List Chunk) := #[
  [⟨1, 148, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨149, 158, ⟨0, 3, false, true, false, 149, 149⟩⟩,
   ⟨159, 255, ⟨3, 7, false, true, false, 159, 159⟩⟩,
   ⟨256, 340, ⟨3, 7, false, false, false, 256, 256⟩⟩],
  [⟨68, 148, ⟨0, 3, true, true, false, 148, 148⟩⟩,
   ⟨149, 192, ⟨0, 3, false, true, false, 192, 192⟩⟩,
   ⟨193, 255, ⟨3, 7, false, true, false, 193, 193⟩⟩,
   ⟨256, 374, ⟨3, 7, false, false, false, 256, 256⟩⟩],
  [⟨101, 148, ⟨0, 2, true, true, false, 148, 148⟩⟩,
   ⟨149, 192, ⟨0, 2, false, true, false, 192, 192⟩⟩,
   ⟨193, 255, ⟨2, 7, false, true, false, 193, 193⟩⟩,
   ⟨256, 407, ⟨2, 7, false, false, false, 256, 256⟩⟩],
  [⟨135, 148, ⟨0, 2, true, true, false, 148, 148⟩⟩,
   ⟨149, 225, ⟨0, 2, false, true, false, 225, 225⟩⟩,
   ⟨226, 255, ⟨2, 7, false, true, false, 255, 255⟩⟩,
   ⟨256, 474, ⟨2, 7, false, false, false, 474, 474⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_193_lower : ConfigurationBounds 193 3515 104 := by
  apply configuration_of_cells 193 3515 104 data_193_lower
  decide +kernel

private def data_194_lower : Array (List Chunk) := #[
  [⟨1, 148, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨149, 159, ⟨0, 3, false, true, false, 149, 149⟩⟩,
   ⟨160, 254, ⟨3, 7, false, true, false, 160, 160⟩⟩,
   ⟨255, 343, ⟨3, 7, false, false, false, 255, 255⟩⟩],
  [⟨68, 148, ⟨0, 3, true, true, false, 148, 148⟩⟩,
   ⟨149, 193, ⟨0, 3, false, true, false, 193, 193⟩⟩,
   ⟨194, 254, ⟨3, 7, false, true, false, 194, 194⟩⟩,
   ⟨255, 377, ⟨3, 7, false, false, false, 255, 255⟩⟩],
  [⟨101, 148, ⟨0, 2, true, true, false, 148, 148⟩⟩,
   ⟨149, 193, ⟨0, 2, false, true, false, 193, 193⟩⟩,
   ⟨194, 254, ⟨2, 7, false, true, false, 194, 194⟩⟩,
   ⟨255, 410, ⟨2, 7, false, false, false, 255, 255⟩⟩],
  [⟨135, 148, ⟨0, 2, true, true, false, 148, 148⟩⟩,
   ⟨149, 226, ⟨0, 2, false, true, false, 226, 226⟩⟩,
   ⟨227, 254, ⟨2, 7, false, true, false, 254, 254⟩⟩,
   ⟨255, 477, ⟨2, 7, false, false, false, 477, 477⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_194_lower : ConfigurationBounds 194 3551 104 := by
  apply configuration_of_cells 194 3551 104 data_194_lower
  decide +kernel

private def data_195_lower : Array (List Chunk) := #[
  [⟨1, 149, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨150, 160, ⟨0, 3, false, true, false, 150, 150⟩⟩,
   ⟨161, 346, ⟨3, 7, false, true, false, 161, 161⟩⟩],
  [⟨68, 149, ⟨0, 3, true, true, false, 149, 149⟩⟩,
   ⟨150, 194, ⟨0, 3, false, true, false, 194, 194⟩⟩,
   ⟨195, 374, ⟨3, 7, false, true, false, 195, 195⟩⟩,
   ⟨375, 380, ⟨3, 7, false, false, false, 375, 375⟩⟩],
  [⟨101, 149, ⟨0, 2, true, true, false, 149, 149⟩⟩,
   ⟨150, 194, ⟨0, 2, false, true, false, 194, 194⟩⟩,
   ⟨195, 374, ⟨2, 7, false, true, false, 195, 195⟩⟩,
   ⟨375, 413, ⟨2, 7, false, false, false, 375, 375⟩⟩],
  [⟨135, 149, ⟨0, 2, true, true, false, 149, 149⟩⟩,
   ⟨150, 227, ⟨0, 2, false, true, false, 227, 227⟩⟩,
   ⟨228, 374, ⟨2, 7, false, true, false, 374, 374⟩⟩,
   ⟨375, 480, ⟨2, 7, false, false, false, 480, 480⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_195_lower : ConfigurationBounds 195 3588 104 := by
  apply configuration_of_cells 195 3588 104 data_195_lower
  decide +kernel

private def data_196_lower : Array (List Chunk) := #[
  [⟨1, 150, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨151, 161, ⟨0, 3, false, true, false, 151, 151⟩⟩,
   ⟨162, 321, ⟨3, 7, false, true, false, 162, 162⟩⟩,
   ⟨322, 347, ⟨3, 7, false, false, false, 322, 322⟩⟩],
  [⟨68, 150, ⟨0, 3, true, true, false, 150, 150⟩⟩,
   ⟨151, 195, ⟨0, 3, false, true, false, 195, 195⟩⟩,
   ⟨196, 321, ⟨3, 7, false, true, false, 196, 196⟩⟩,
   ⟨322, 381, ⟨3, 7, false, false, false, 322, 322⟩⟩],
  [⟨102, 150, ⟨0, 2, true, true, false, 150, 150⟩⟩,
   ⟨151, 195, ⟨0, 2, false, true, false, 195, 195⟩⟩,
   ⟨196, 321, ⟨2, 7, false, true, false, 196, 196⟩⟩,
   ⟨322, 415, ⟨2, 7, false, false, false, 322, 322⟩⟩],
  [⟨136, 150, ⟨0, 2, true, true, false, 150, 150⟩⟩,
   ⟨151, 229, ⟨0, 2, false, true, false, 229, 229⟩⟩,
   ⟨230, 321, ⟨2, 7, false, true, false, 321, 321⟩⟩,
   ⟨322, 482, ⟨2, 7, false, false, false, 482, 482⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_196_lower : ConfigurationBounds 196 3624 105 := by
  apply configuration_of_cells 196 3624 105 data_196_lower
  decide +kernel

private def data_197_lower : Array (List Chunk) := #[
  [⟨1, 151, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨152, 161, ⟨0, 3, false, true, false, 152, 152⟩⟩,
   ⟨162, 240, ⟨3, 7, false, true, false, 162, 162⟩⟩,
   ⟨241, 347, ⟨3, 7, false, false, false, 241, 241⟩⟩],
  [⟨69, 151, ⟨0, 3, true, true, false, 151, 151⟩⟩,
   ⟨152, 196, ⟨0, 3, false, true, false, 196, 196⟩⟩,
   ⟨197, 240, ⟨3, 7, false, true, false, 197, 197⟩⟩,
   ⟨241, 382, ⟨3, 7, false, false, false, 241, 241⟩⟩],
  [⟨103, 151, ⟨0, 2, true, true, false, 151, 151⟩⟩,
   ⟨152, 196, ⟨0, 2, false, true, false, 196, 196⟩⟩,
   ⟨197, 240, ⟨2, 7, false, true, false, 197, 197⟩⟩,
   ⟨241, 416, ⟨2, 7, false, false, false, 241, 241⟩⟩],
  [⟨138, 151, ⟨0, 2, true, true, false, 151, 151⟩⟩,
   ⟨152, 230, ⟨0, 2, false, true, false, 230, 230⟩⟩,
   ⟨231, 240, ⟨2, 7, false, true, false, 240, 240⟩⟩,
   ⟨241, 484, ⟨2, 7, false, false, false, 484, 484⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_197_lower : ConfigurationBounds 197 3660 106 := by
  apply configuration_of_cells 197 3660 106 data_197_lower
  decide +kernel

private def data_198_lower : Array (List Chunk) := #[
  [⟨1, 152, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨153, 162, ⟨0, 3, false, true, false, 153, 153⟩⟩,
   ⟨163, 281, ⟨3, 7, false, true, false, 163, 163⟩⟩,
   ⟨282, 348, ⟨3, 7, false, false, false, 282, 282⟩⟩],
  [⟨70, 152, ⟨0, 3, true, true, false, 152, 152⟩⟩,
   ⟨153, 197, ⟨0, 3, false, true, false, 197, 197⟩⟩,
   ⟨198, 281, ⟨3, 7, false, true, false, 198, 198⟩⟩,
   ⟨282, 383, ⟨3, 7, false, false, false, 282, 282⟩⟩],
  [⟨104, 152, ⟨0, 2, true, true, false, 152, 152⟩⟩,
   ⟨153, 197, ⟨0, 2, false, true, false, 197, 197⟩⟩,
   ⟨198, 281, ⟨2, 7, false, true, false, 198, 198⟩⟩,
   ⟨282, 417, ⟨2, 7, false, false, false, 282, 282⟩⟩],
  [⟨139, 152, ⟨0, 2, true, true, false, 152, 152⟩⟩,
   ⟨153, 231, ⟨0, 2, false, true, false, 231, 231⟩⟩,
   ⟨232, 281, ⟨2, 7, false, true, false, 281, 281⟩⟩,
   ⟨282, 486, ⟨2, 7, false, false, false, 486, 486⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_198_lower : ConfigurationBounds 198 3697 107 := by
  apply configuration_of_cells 198 3697 107 data_198_lower
  decide +kernel

private def data_199_lower : Array (List Chunk) := #[
  [⟨1, 152, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨153, 163, ⟨0, 3, false, true, false, 153, 153⟩⟩,
   ⟨164, 292, ⟨3, 7, false, true, false, 164, 164⟩⟩,
   ⟨293, 351, ⟨3, 7, false, false, false, 293, 293⟩⟩],
  [⟨70, 152, ⟨0, 3, true, true, false, 152, 152⟩⟩,
   ⟨153, 198, ⟨0, 3, false, true, false, 198, 198⟩⟩,
   ⟨199, 292, ⟨3, 7, false, true, false, 199, 199⟩⟩,
   ⟨293, 386, ⟨3, 7, false, false, false, 293, 293⟩⟩],
  [⟨104, 152, ⟨0, 2, true, true, false, 152, 152⟩⟩,
   ⟨153, 198, ⟨0, 2, false, true, false, 198, 198⟩⟩,
   ⟨199, 292, ⟨2, 7, false, true, false, 199, 199⟩⟩,
   ⟨293, 420, ⟨2, 7, false, false, false, 293, 293⟩⟩],
  [⟨139, 152, ⟨0, 2, true, true, false, 152, 152⟩⟩,
   ⟨153, 232, ⟨0, 2, false, true, false, 232, 232⟩⟩,
   ⟨233, 292, ⟨2, 7, false, true, false, 292, 292⟩⟩,
   ⟨293, 489, ⟨2, 7, false, false, false, 489, 489⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_199_lower : ConfigurationBounds 199 3734 107 := by
  apply configuration_of_cells 199 3734 107 data_199_lower
  decide +kernel

private def data_200_lower : Array (List Chunk) := #[
  [⟨1, 153, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨154, 164, ⟨0, 3, false, true, false, 154, 154⟩⟩,
   ⟨165, 278, ⟨3, 7, false, true, false, 165, 165⟩⟩,
   ⟨279, 352, ⟨3, 7, false, false, false, 279, 279⟩⟩],
  [⟨70, 153, ⟨0, 3, true, true, false, 153, 153⟩⟩,
   ⟨154, 199, ⟨0, 3, false, true, false, 199, 199⟩⟩,
   ⟨200, 278, ⟨3, 7, false, true, false, 200, 200⟩⟩,
   ⟨279, 387, ⟨3, 7, false, false, false, 279, 279⟩⟩],
  [⟨105, 153, ⟨0, 2, true, true, false, 153, 153⟩⟩,
   ⟨154, 199, ⟨0, 2, false, true, false, 199, 199⟩⟩,
   ⟨200, 278, ⟨2, 7, false, true, false, 200, 200⟩⟩,
   ⟨279, 422, ⟨2, 7, false, false, false, 279, 279⟩⟩],
  [⟨140, 153, ⟨0, 2, true, true, false, 153, 153⟩⟩,
   ⟨154, 234, ⟨0, 2, false, true, false, 234, 234⟩⟩,
   ⟨235, 278, ⟨2, 7, false, true, false, 278, 278⟩⟩,
   ⟨279, 491, ⟨2, 7, false, false, false, 491, 491⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_200_lower : ConfigurationBounds 200 3771 108 := by
  apply configuration_of_cells 200 3771 108 data_200_lower
  decide +kernel

private def data_201_lower : Array (List Chunk) := #[
  [⟨1, 154, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨155, 165, ⟨0, 3, false, true, false, 155, 155⟩⟩,
   ⟨166, 355, ⟨3, 7, false, true, false, 166, 166⟩⟩],
  [⟨70, 154, ⟨0, 3, true, true, false, 154, 154⟩⟩,
   ⟨155, 200, ⟨0, 3, false, true, false, 200, 200⟩⟩,
   ⟨201, 386, ⟨3, 7, false, true, false, 201, 201⟩⟩,
   ⟨387, 390, ⟨3, 7, false, false, false, 387, 387⟩⟩],
  [⟨105, 154, ⟨0, 2, true, true, false, 154, 154⟩⟩,
   ⟨155, 200, ⟨0, 2, false, true, false, 200, 200⟩⟩,
   ⟨201, 386, ⟨2, 7, false, true, false, 201, 201⟩⟩,
   ⟨387, 425, ⟨2, 7, false, false, false, 387, 387⟩⟩],
  [⟨140, 154, ⟨0, 2, true, true, false, 154, 154⟩⟩,
   ⟨155, 235, ⟨0, 2, false, true, false, 235, 235⟩⟩,
   ⟨236, 386, ⟨2, 7, false, true, false, 386, 386⟩⟩,
   ⟨387, 494, ⟨2, 7, false, false, false, 494, 494⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_201_lower : ConfigurationBounds 201 3809 108 := by
  apply configuration_of_cells 201 3809 108 data_201_lower
  decide +kernel

private def data_202_lower : Array (List Chunk) := #[
  [⟨1, 155, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨156, 165, ⟨0, 3, false, true, false, 156, 156⟩⟩,
   ⟨166, 316, ⟨3, 7, false, true, false, 166, 166⟩⟩,
   ⟨317, 355, ⟨3, 7, false, false, false, 317, 317⟩⟩],
  [⟨71, 155, ⟨0, 3, true, true, false, 155, 155⟩⟩,
   ⟨156, 201, ⟨0, 3, false, true, false, 201, 201⟩⟩,
   ⟨202, 316, ⟨3, 7, false, true, false, 202, 202⟩⟩,
   ⟨317, 391, ⟨3, 7, false, false, false, 317, 317⟩⟩],
  [⟨106, 155, ⟨0, 2, true, true, false, 155, 155⟩⟩,
   ⟨156, 201, ⟨0, 2, false, true, false, 201, 201⟩⟩,
   ⟨202, 316, ⟨2, 7, false, true, false, 202, 202⟩⟩,
   ⟨317, 426, ⟨2, 7, false, false, false, 317, 317⟩⟩],
  [⟨142, 155, ⟨0, 2, true, true, false, 155, 155⟩⟩,
   ⟨156, 236, ⟨0, 2, false, true, false, 236, 236⟩⟩,
   ⟨237, 316, ⟨2, 7, false, true, false, 316, 316⟩⟩,
   ⟨317, 496, ⟨2, 7, false, false, false, 496, 496⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_202_lower : ConfigurationBounds 202 3846 109 := by
  apply configuration_of_cells 202 3846 109 data_202_lower
  decide +kernel

private def data_203_lower : Array (List Chunk) := #[
  [⟨1, 155, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨156, 166, ⟨0, 3, false, true, false, 156, 156⟩⟩,
   ⟨167, 358, ⟨3, 7, false, true, false, 167, 167⟩⟩],
  [⟨71, 155, ⟨0, 3, true, true, false, 155, 155⟩⟩,
   ⟨156, 202, ⟨0, 3, false, true, false, 202, 202⟩⟩,
   ⟨203, 369, ⟨3, 7, false, true, false, 203, 203⟩⟩,
   ⟨370, 394, ⟨3, 7, false, false, false, 370, 370⟩⟩],
  [⟨106, 155, ⟨0, 2, true, true, false, 155, 155⟩⟩,
   ⟨156, 202, ⟨0, 2, false, true, false, 202, 202⟩⟩,
   ⟨203, 369, ⟨2, 7, false, true, false, 203, 203⟩⟩,
   ⟨370, 429, ⟨2, 7, false, false, false, 370, 370⟩⟩],
  [⟨142, 155, ⟨0, 2, true, true, false, 155, 155⟩⟩,
   ⟨156, 237, ⟨0, 2, false, true, false, 237, 237⟩⟩,
   ⟨238, 369, ⟨2, 7, false, true, false, 369, 369⟩⟩,
   ⟨370, 499, ⟨2, 7, false, false, false, 499, 499⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_203_lower : ConfigurationBounds 203 3884 109 := by
  apply configuration_of_cells 203 3884 109 data_203_lower
  decide +kernel

private def data_204_lower : Array (List Chunk) := #[
  [⟨1, 156, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨157, 167, ⟨0, 3, false, true, false, 157, 157⟩⟩,
   ⟨168, 361, ⟨3, 7, false, true, false, 168, 168⟩⟩],
  [⟨71, 156, ⟨0, 3, true, true, false, 156, 156⟩⟩,
   ⟨157, 203, ⟨0, 3, false, true, false, 203, 203⟩⟩,
   ⟨204, 395, ⟨3, 7, false, true, false, 204, 204⟩⟩,
   ⟨396, 397, ⟨3, 7, false, false, false, 396, 396⟩⟩],
  [⟨106, 156, ⟨0, 2, true, true, false, 156, 156⟩⟩,
   ⟨157, 203, ⟨0, 2, false, true, false, 203, 203⟩⟩,
   ⟨204, 395, ⟨2, 7, false, true, false, 204, 204⟩⟩,
   ⟨396, 432, ⟨2, 7, false, false, false, 396, 396⟩⟩],
  [⟨142, 156, ⟨0, 2, true, true, false, 156, 156⟩⟩,
   ⟨157, 238, ⟨0, 2, false, true, false, 238, 238⟩⟩,
   ⟨239, 395, ⟨2, 7, false, true, false, 395, 395⟩⟩,
   ⟨396, 502, ⟨2, 7, false, false, false, 502, 502⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_204_lower : ConfigurationBounds 204 3922 109 := by
  apply configuration_of_cells 204 3922 109 data_204_lower
  decide +kernel

private def data_205_lower : Array (List Chunk) := #[
  [⟨1, 157, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨158, 168, ⟨0, 3, false, true, false, 158, 158⟩⟩,
   ⟨169, 362, ⟨3, 7, false, true, false, 169, 169⟩⟩],
  [⟨72, 157, ⟨0, 3, true, true, false, 157, 157⟩⟩,
   ⟨158, 204, ⟨0, 3, false, true, false, 204, 204⟩⟩,
   ⟨205, 393, ⟨3, 7, false, true, false, 205, 205⟩⟩,
   ⟨394, 398, ⟨3, 7, false, false, false, 394, 394⟩⟩],
  [⟨107, 157, ⟨0, 2, true, true, false, 157, 157⟩⟩,
   ⟨158, 204, ⟨0, 2, false, true, false, 204, 204⟩⟩,
   ⟨205, 393, ⟨2, 7, false, true, false, 205, 205⟩⟩,
   ⟨394, 433, ⟨2, 7, false, false, false, 394, 394⟩⟩],
  [⟨143, 157, ⟨0, 2, true, true, false, 157, 157⟩⟩,
   ⟨158, 239, ⟨0, 2, false, true, false, 239, 239⟩⟩,
   ⟨240, 393, ⟨2, 7, false, true, false, 393, 393⟩⟩,
   ⟨394, 504, ⟨2, 7, false, false, false, 504, 504⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_205_lower : ConfigurationBounds 205 3960 110 := by
  apply configuration_of_cells 205 3960 110 data_205_lower
  decide +kernel

private def data_206_lower : Array (List Chunk) := #[
  [⟨1, 158, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨159, 169, ⟨0, 3, false, true, false, 159, 159⟩⟩,
   ⟨170, 363, ⟨3, 7, false, true, false, 170, 170⟩⟩],
  [⟨72, 158, ⟨0, 3, true, true, false, 158, 158⟩⟩,
   ⟨159, 205, ⟨0, 3, false, true, false, 205, 205⟩⟩,
   ⟨206, 363, ⟨3, 7, false, true, false, 206, 206⟩⟩,
   ⟨364, 399, ⟨3, 7, false, false, false, 364, 364⟩⟩],
  [⟨108, 158, ⟨0, 2, true, true, false, 158, 158⟩⟩,
   ⟨159, 205, ⟨0, 2, false, true, false, 205, 205⟩⟩,
   ⟨206, 363, ⟨2, 7, false, true, false, 206, 206⟩⟩,
   ⟨364, 435, ⟨2, 7, false, false, false, 364, 364⟩⟩],
  [⟨144, 158, ⟨0, 2, true, true, false, 158, 158⟩⟩,
   ⟨159, 241, ⟨0, 2, false, true, false, 241, 241⟩⟩,
   ⟨242, 363, ⟨2, 7, false, true, false, 363, 363⟩⟩,
   ⟨364, 506, ⟨2, 7, false, false, false, 506, 506⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_206_lower : ConfigurationBounds 206 3998 111 := by
  apply configuration_of_cells 206 3998 111 data_206_lower
  decide +kernel

private def data_207_lower : Array (List Chunk) := #[
  [⟨1, 158, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨159, 170, ⟨0, 3, false, true, false, 159, 159⟩⟩,
   ⟨171, 302, ⟨3, 7, false, true, false, 171, 171⟩⟩,
   ⟨303, 366, ⟨3, 7, false, false, false, 303, 303⟩⟩],
  [⟨72, 158, ⟨0, 3, true, true, false, 158, 158⟩⟩,
   ⟨159, 206, ⟨0, 3, false, true, false, 206, 206⟩⟩,
   ⟨207, 302, ⟨3, 7, false, true, false, 207, 207⟩⟩,
   ⟨303, 402, ⟨3, 7, false, false, false, 303, 303⟩⟩],
  [⟨108, 158, ⟨0, 2, true, true, false, 158, 158⟩⟩,
   ⟨159, 206, ⟨0, 2, false, true, false, 206, 206⟩⟩,
   ⟨207, 302, ⟨2, 7, false, true, false, 207, 207⟩⟩,
   ⟨303, 438, ⟨2, 7, false, false, false, 303, 303⟩⟩],
  [⟨144, 158, ⟨0, 2, true, true, false, 158, 158⟩⟩,
   ⟨159, 242, ⟨0, 2, false, true, false, 242, 242⟩⟩,
   ⟨243, 302, ⟨2, 7, false, true, false, 302, 302⟩⟩,
   ⟨303, 509, ⟨2, 7, false, false, false, 509, 509⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_207_lower : ConfigurationBounds 207 4036 111 := by
  apply configuration_of_cells 207 4036 111 data_207_lower
  decide +kernel

private def data_208_lower : Array (List Chunk) := #[
  [⟨1, 159, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨160, 170, ⟨0, 3, false, true, false, 160, 160⟩⟩,
   ⟨171, 366, ⟨3, 7, false, true, false, 171, 171⟩⟩],
  [⟨73, 159, ⟨0, 3, true, true, false, 159, 159⟩⟩,
   ⟨160, 207, ⟨0, 3, false, true, false, 207, 207⟩⟩,
   ⟨208, 371, ⟨3, 7, false, true, false, 208, 208⟩⟩,
   ⟨372, 403, ⟨3, 7, false, false, false, 372, 372⟩⟩],
  [⟨109, 159, ⟨0, 2, true, true, false, 159, 159⟩⟩,
   ⟨160, 207, ⟨0, 2, false, true, false, 207, 207⟩⟩,
   ⟨208, 371, ⟨2, 7, false, true, false, 208, 208⟩⟩,
   ⟨372, 439, ⟨2, 7, false, false, false, 372, 372⟩⟩],
  [⟨146, 159, ⟨0, 2, true, true, false, 159, 159⟩⟩,
   ⟨160, 243, ⟨0, 2, false, true, false, 243, 243⟩⟩,
   ⟨244, 371, ⟨2, 7, false, true, false, 371, 371⟩⟩,
   ⟨372, 511, ⟨2, 7, false, false, false, 511, 511⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_208_lower : ConfigurationBounds 208 4075 112 := by
  apply configuration_of_cells 208 4075 112 data_208_lower
  decide +kernel

private def data_209_lower : Array (List Chunk) := #[
  [⟨1, 160, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨161, 171, ⟨0, 3, false, true, false, 161, 161⟩⟩,
   ⟨172, 369, ⟨3, 7, false, true, false, 172, 172⟩⟩],
  [⟨73, 160, ⟨0, 3, true, true, false, 160, 160⟩⟩,
   ⟨161, 208, ⟨0, 3, false, true, false, 208, 208⟩⟩,
   ⟨209, 406, ⟨3, 7, false, true, false, 209, 209⟩⟩],
  [⟨109, 160, ⟨0, 2, true, true, false, 160, 160⟩⟩,
   ⟨161, 208, ⟨0, 2, false, true, false, 208, 208⟩⟩,
   ⟨209, 410, ⟨2, 7, false, true, false, 209, 209⟩⟩,
   ⟨411, 442, ⟨2, 7, false, false, false, 411, 411⟩⟩],
  [⟨146, 160, ⟨0, 2, true, true, false, 160, 160⟩⟩,
   ⟨161, 244, ⟨0, 2, false, true, false, 244, 244⟩⟩,
   ⟨245, 410, ⟨2, 7, false, true, false, 410, 410⟩⟩,
   ⟨411, 514, ⟨2, 7, false, false, false, 514, 514⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_209_lower : ConfigurationBounds 209 4114 112 := by
  apply configuration_of_cells 209 4114 112 data_209_lower
  decide +kernel

private def data_210_lower : Array (List Chunk) := #[
  [⟨1, 161, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨162, 172, ⟨0, 3, false, true, false, 162, 162⟩⟩,
   ⟨173, 262, ⟨3, 7, false, true, false, 173, 173⟩⟩,
   ⟨263, 370, ⟨3, 7, false, false, false, 263, 263⟩⟩],
  [⟨74, 161, ⟨0, 3, true, true, false, 161, 161⟩⟩,
   ⟨162, 209, ⟨0, 3, false, true, false, 209, 209⟩⟩,
   ⟨210, 262, ⟨3, 7, false, true, false, 210, 210⟩⟩,
   ⟨263, 407, ⟨3, 7, false, false, false, 263, 263⟩⟩],
  [⟨110, 161, ⟨0, 2, true, true, false, 161, 161⟩⟩,
   ⟨162, 209, ⟨0, 2, false, true, false, 209, 209⟩⟩,
   ⟨210, 262, ⟨2, 7, false, true, false, 210, 210⟩⟩,
   ⟨263, 443, ⟨2, 7, false, false, false, 263, 263⟩⟩],
  [⟨147, 161, ⟨0, 2, true, true, false, 161, 161⟩⟩,
   ⟨162, 245, ⟨0, 2, false, true, false, 245, 245⟩⟩,
   ⟨246, 262, ⟨2, 7, false, true, false, 262, 262⟩⟩,
   ⟨263, 516, ⟨2, 7, false, false, false, 516, 516⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_210_lower : ConfigurationBounds 210 4152 113 := by
  apply configuration_of_cells 210 4152 113 data_210_lower
  decide +kernel

private def data_211_lower : Array (List Chunk) := #[
  [⟨1, 161, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨162, 173, ⟨0, 3, false, true, false, 162, 162⟩⟩,
   ⟨174, 373, ⟨3, 7, false, true, false, 174, 174⟩⟩],
  [⟨74, 161, ⟨0, 3, true, true, false, 161, 161⟩⟩,
   ⟨162, 210, ⟨0, 3, false, true, false, 210, 210⟩⟩,
   ⟨211, 403, ⟨3, 7, false, true, false, 211, 211⟩⟩,
   ⟨404, 410, ⟨3, 7, false, false, false, 404, 404⟩⟩],
  [⟨110, 161, ⟨0, 2, true, true, false, 161, 161⟩⟩,
   ⟨162, 210, ⟨0, 2, false, true, false, 210, 210⟩⟩,
   ⟨211, 403, ⟨2, 7, false, true, false, 211, 211⟩⟩,
   ⟨404, 446, ⟨2, 7, false, false, false, 404, 404⟩⟩],
  [⟨147, 161, ⟨0, 2, true, true, false, 161, 161⟩⟩,
   ⟨162, 246, ⟨0, 2, false, true, false, 246, 246⟩⟩,
   ⟨247, 403, ⟨2, 7, false, true, false, 403, 403⟩⟩,
   ⟨404, 519, ⟨2, 7, false, false, false, 519, 519⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_211_lower : ConfigurationBounds 211 4192 113 := by
  apply configuration_of_cells 211 4192 113 data_211_lower
  decide +kernel

private def data_212_lower : Array (List Chunk) := #[
  [⟨1, 162, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨163, 174, ⟨0, 3, false, true, false, 163, 163⟩⟩,
   ⟨175, 355, ⟨3, 7, false, true, false, 175, 175⟩⟩,
   ⟨356, 374, ⟨3, 7, false, false, false, 356, 356⟩⟩],
  [⟨74, 162, ⟨0, 3, true, true, false, 162, 162⟩⟩,
   ⟨163, 211, ⟨0, 3, false, true, false, 211, 211⟩⟩,
   ⟨212, 355, ⟨3, 7, false, true, false, 212, 212⟩⟩,
   ⟨356, 411, ⟨3, 7, false, false, false, 356, 356⟩⟩],
  [⟨111, 162, ⟨0, 2, true, true, false, 162, 162⟩⟩,
   ⟨163, 211, ⟨0, 2, false, true, false, 211, 211⟩⟩,
   ⟨212, 355, ⟨2, 7, false, true, false, 212, 212⟩⟩,
   ⟨356, 448, ⟨2, 7, false, false, false, 356, 356⟩⟩],
  [⟨148, 162, ⟨0, 2, true, true, false, 162, 162⟩⟩,
   ⟨163, 248, ⟨0, 2, false, true, false, 248, 248⟩⟩,
   ⟨249, 355, ⟨2, 7, false, true, false, 355, 355⟩⟩,
   ⟨356, 521, ⟨2, 7, false, false, false, 521, 521⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_212_lower : ConfigurationBounds 212 4231 114 := by
  apply configuration_of_cells 212 4231 114 data_212_lower
  decide +kernel

private def data_213_lower : Array (List Chunk) := #[
  [⟨1, 163, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨164, 174, ⟨0, 3, false, true, false, 164, 164⟩⟩,
   ⟨175, 278, ⟨3, 7, false, true, false, 175, 175⟩⟩,
   ⟨279, 374, ⟨3, 7, false, false, false, 279, 279⟩⟩],
  [⟨75, 163, ⟨0, 3, true, true, false, 163, 163⟩⟩,
   ⟨164, 212, ⟨0, 3, false, true, false, 212, 212⟩⟩,
   ⟨213, 278, ⟨3, 7, false, true, false, 213, 213⟩⟩,
   ⟨279, 412, ⟨3, 7, false, false, false, 279, 279⟩⟩],
  [⟨112, 163, ⟨0, 2, true, true, false, 163, 163⟩⟩,
   ⟨164, 212, ⟨0, 2, false, true, false, 212, 212⟩⟩,
   ⟨213, 278, ⟨2, 7, false, true, false, 213, 213⟩⟩,
   ⟨279, 449, ⟨2, 7, false, false, false, 279, 279⟩⟩],
  [⟨150, 163, ⟨0, 2, true, true, false, 163, 163⟩⟩,
   ⟨164, 249, ⟨0, 2, false, true, false, 249, 249⟩⟩,
   ⟨250, 278, ⟨2, 7, false, true, false, 278, 278⟩⟩,
   ⟨279, 523, ⟨2, 7, false, false, false, 523, 523⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_213_lower : ConfigurationBounds 213 4270 115 := by
  apply configuration_of_cells 213 4270 115 data_213_lower
  decide +kernel

private def data_214_lower : Array (List Chunk) := #[
  [⟨1, 164, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨165, 175, ⟨0, 3, false, true, false, 165, 165⟩⟩,
   ⟨176, 330, ⟨3, 7, false, true, false, 176, 176⟩⟩,
   ⟨331, 377, ⟨3, 7, false, false, false, 331, 331⟩⟩],
  [⟨75, 164, ⟨0, 3, true, true, false, 164, 164⟩⟩,
   ⟨165, 213, ⟨0, 3, false, true, false, 213, 213⟩⟩,
   ⟨214, 330, ⟨3, 7, false, true, false, 214, 214⟩⟩,
   ⟨331, 415, ⟨3, 7, false, false, false, 331, 331⟩⟩],
  [⟨112, 164, ⟨0, 2, true, true, false, 164, 164⟩⟩,
   ⟨165, 213, ⟨0, 2, false, true, false, 213, 213⟩⟩,
   ⟨214, 330, ⟨2, 7, false, true, false, 214, 214⟩⟩,
   ⟨331, 452, ⟨2, 7, false, false, false, 331, 331⟩⟩],
  [⟨150, 164, ⟨0, 2, true, true, false, 164, 164⟩⟩,
   ⟨165, 250, ⟨0, 2, false, true, false, 250, 250⟩⟩,
   ⟨251, 330, ⟨2, 7, false, true, false, 330, 330⟩⟩,
   ⟨331, 526, ⟨2, 7, false, false, false, 526, 526⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_214_lower : ConfigurationBounds 214 4310 115 := by
  apply configuration_of_cells 214 4310 115 data_214_lower
  decide +kernel

private def data_215_lower : Array (List Chunk) := #[
  [⟨1, 165, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨166, 176, ⟨0, 3, false, true, false, 166, 166⟩⟩,
   ⟨177, 355, ⟨3, 7, false, true, false, 177, 177⟩⟩,
   ⟨356, 378, ⟨3, 7, false, false, false, 356, 356⟩⟩],
  [⟨76, 165, ⟨0, 3, true, true, false, 165, 165⟩⟩,
   ⟨166, 214, ⟨0, 3, false, true, false, 214, 214⟩⟩,
   ⟨215, 355, ⟨3, 7, false, true, false, 215, 215⟩⟩,
   ⟨356, 416, ⟨3, 7, false, false, false, 356, 356⟩⟩],
  [⟨113, 165, ⟨0, 2, true, true, false, 165, 165⟩⟩,
   ⟨166, 214, ⟨0, 2, false, true, false, 214, 214⟩⟩,
   ⟨215, 355, ⟨2, 7, false, true, false, 215, 215⟩⟩,
   ⟨356, 453, ⟨2, 7, false, false, false, 356, 356⟩⟩],
  [⟨151, 165, ⟨0, 2, true, true, false, 165, 165⟩⟩,
   ⟨166, 251, ⟨0, 2, false, true, false, 251, 251⟩⟩,
   ⟨252, 355, ⟨2, 7, false, true, false, 355, 355⟩⟩,
   ⟨356, 528, ⟨2, 7, false, false, false, 528, 528⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_215_lower : ConfigurationBounds 215 4350 116 := by
  apply configuration_of_cells 215 4350 116 data_215_lower
  decide +kernel

private def data_216_lower : Array (List Chunk) := #[
  [⟨1, 165, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨166, 177, ⟨0, 3, false, true, false, 166, 166⟩⟩,
   ⟨178, 348, ⟨3, 7, false, true, false, 178, 178⟩⟩,
   ⟨349, 381, ⟨3, 7, false, false, false, 349, 349⟩⟩],
  [⟨76, 165, ⟨0, 3, true, true, false, 165, 165⟩⟩,
   ⟨166, 215, ⟨0, 3, false, true, false, 215, 215⟩⟩,
   ⟨216, 348, ⟨3, 7, false, true, false, 216, 216⟩⟩,
   ⟨349, 419, ⟨3, 7, false, false, false, 349, 349⟩⟩],
  [⟨113, 165, ⟨0, 2, true, true, false, 165, 165⟩⟩,
   ⟨166, 215, ⟨0, 2, false, true, false, 215, 215⟩⟩,
   ⟨216, 348, ⟨2, 7, false, true, false, 216, 216⟩⟩,
   ⟨349, 456, ⟨2, 7, false, false, false, 349, 349⟩⟩],
  [⟨151, 165, ⟨0, 2, true, true, false, 165, 165⟩⟩,
   ⟨166, 252, ⟨0, 2, false, true, false, 252, 252⟩⟩,
   ⟨253, 348, ⟨2, 7, false, true, false, 348, 348⟩⟩,
   ⟨349, 531, ⟨2, 7, false, false, false, 531, 531⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_216_lower : ConfigurationBounds 216 4390 116 := by
  apply configuration_of_cells 216 4390 116 data_216_lower
  decide +kernel

private def data_217_lower : Array (List Chunk) := #[
  [⟨1, 166, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨167, 178, ⟨0, 3, false, true, false, 167, 167⟩⟩,
   ⟨179, 313, ⟨3, 7, false, true, false, 179, 179⟩⟩,
   ⟨314, 382, ⟨3, 7, false, false, false, 314, 314⟩⟩],
  [⟨76, 166, ⟨0, 3, true, true, false, 166, 166⟩⟩,
   ⟨167, 216, ⟨0, 3, false, true, false, 216, 216⟩⟩,
   ⟨217, 313, ⟨3, 7, false, true, false, 217, 217⟩⟩,
   ⟨314, 420, ⟨3, 7, false, false, false, 314, 314⟩⟩],
  [⟨114, 166, ⟨0, 2, true, true, false, 166, 166⟩⟩,
   ⟨167, 216, ⟨0, 2, false, true, false, 216, 216⟩⟩,
   ⟨217, 313, ⟨2, 7, false, true, false, 217, 217⟩⟩,
   ⟨314, 458, ⟨2, 7, false, false, false, 314, 314⟩⟩],
  [⟨152, 166, ⟨0, 2, true, true, false, 166, 166⟩⟩,
   ⟨167, 254, ⟨0, 2, false, true, false, 254, 254⟩⟩,
   ⟨255, 313, ⟨2, 7, false, true, false, 313, 313⟩⟩,
   ⟨314, 533, ⟨2, 7, false, false, false, 533, 533⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_217_lower : ConfigurationBounds 217 4430 117 := by
  apply configuration_of_cells 217 4430 117 data_217_lower
  decide +kernel

private def data_218_lower : Array (List Chunk) := #[
  [⟨1, 167, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨168, 179, ⟨0, 3, false, true, false, 168, 168⟩⟩,
   ⟨180, 385, ⟨3, 7, false, true, false, 180, 180⟩⟩],
  [⟨76, 167, ⟨0, 3, true, true, false, 167, 167⟩⟩,
   ⟨168, 217, ⟨0, 3, false, true, false, 217, 217⟩⟩,
   ⟨218, 411, ⟨3, 7, false, true, false, 218, 218⟩⟩,
   ⟨412, 423, ⟨3, 7, false, false, false, 412, 412⟩⟩],
  [⟨114, 167, ⟨0, 2, true, true, false, 167, 167⟩⟩,
   ⟨168, 217, ⟨0, 2, false, true, false, 217, 217⟩⟩,
   ⟨218, 411, ⟨2, 7, false, true, false, 218, 218⟩⟩,
   ⟨412, 461, ⟨2, 7, false, false, false, 412, 412⟩⟩],
  [⟨152, 167, ⟨0, 2, true, true, false, 167, 167⟩⟩,
   ⟨168, 255, ⟨0, 2, false, true, false, 255, 255⟩⟩,
   ⟨256, 411, ⟨2, 7, false, true, false, 411, 411⟩⟩,
   ⟨412, 536, ⟨2, 7, false, false, false, 536, 536⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_218_lower : ConfigurationBounds 218 4471 117 := by
  apply configuration_of_cells 218 4471 117 data_218_lower
  decide +kernel

private def data_219_lower : Array (List Chunk) := #[
  [⟨1, 168, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨169, 179, ⟨0, 3, false, true, false, 169, 169⟩⟩,
   ⟨180, 315, ⟨3, 7, false, true, false, 180, 180⟩⟩,
   ⟨316, 385, ⟨3, 7, false, false, false, 316, 316⟩⟩],
  [⟨77, 168, ⟨0, 3, true, true, false, 168, 168⟩⟩,
   ⟨169, 218, ⟨0, 3, false, true, false, 218, 218⟩⟩,
   ⟨219, 315, ⟨3, 7, false, true, false, 219, 219⟩⟩,
   ⟨316, 424, ⟨3, 7, false, false, false, 316, 316⟩⟩],
  [⟨115, 168, ⟨0, 2, true, true, false, 168, 168⟩⟩,
   ⟨169, 218, ⟨0, 2, false, true, false, 218, 218⟩⟩,
   ⟨219, 315, ⟨2, 7, false, true, false, 219, 219⟩⟩,
   ⟨316, 462, ⟨2, 7, false, false, false, 316, 316⟩⟩],
  [⟨154, 168, ⟨0, 2, true, true, false, 168, 168⟩⟩,
   ⟨169, 256, ⟨0, 2, false, true, false, 256, 256⟩⟩,
   ⟨257, 315, ⟨2, 7, false, true, false, 315, 315⟩⟩,
   ⟨316, 538, ⟨2, 7, false, false, false, 538, 538⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_219_lower : ConfigurationBounds 219 4511 118 := by
  apply configuration_of_cells 219 4511 118 data_219_lower
  decide +kernel

private def data_220_lower : Array (List Chunk) := #[
  [⟨1, 168, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨169, 180, ⟨0, 3, false, true, false, 169, 169⟩⟩,
   ⟨181, 352, ⟨3, 7, false, true, false, 181, 181⟩⟩,
   ⟨353, 388, ⟨3, 7, false, false, false, 353, 353⟩⟩],
  [⟨77, 168, ⟨0, 3, true, true, false, 168, 168⟩⟩,
   ⟨169, 219, ⟨0, 3, false, true, false, 219, 219⟩⟩,
   ⟨220, 352, ⟨3, 7, false, true, false, 220, 220⟩⟩,
   ⟨353, 427, ⟨3, 7, false, false, false, 353, 353⟩⟩],
  [⟨115, 168, ⟨0, 2, true, true, false, 168, 168⟩⟩,
   ⟨169, 219, ⟨0, 2, false, true, false, 219, 219⟩⟩,
   ⟨220, 352, ⟨2, 7, false, true, false, 220, 220⟩⟩,
   ⟨353, 465, ⟨2, 7, false, false, false, 353, 353⟩⟩],
  [⟨154, 168, ⟨0, 2, true, true, false, 168, 168⟩⟩,
   ⟨169, 257, ⟨0, 2, false, true, false, 257, 257⟩⟩,
   ⟨258, 352, ⟨2, 7, false, true, false, 352, 352⟩⟩,
   ⟨353, 541, ⟨2, 7, false, false, false, 541, 541⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_220_lower : ConfigurationBounds 220 4552 118 := by
  apply configuration_of_cells 220 4552 118 data_220_lower
  decide +kernel

private def data_221_lower : Array (List Chunk) := #[
  [⟨1, 169, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨170, 181, ⟨0, 3, false, true, false, 170, 170⟩⟩,
   ⟨182, 361, ⟨3, 7, false, true, false, 182, 182⟩⟩,
   ⟨362, 389, ⟨3, 7, false, false, false, 362, 362⟩⟩],
  [⟨78, 169, ⟨0, 3, true, true, false, 169, 169⟩⟩,
   ⟨170, 220, ⟨0, 3, false, true, false, 220, 220⟩⟩,
   ⟨221, 361, ⟨3, 7, false, true, false, 221, 221⟩⟩,
   ⟨362, 428, ⟨3, 7, false, false, false, 362, 362⟩⟩],
  [⟨116, 169, ⟨0, 2, true, true, false, 169, 169⟩⟩,
   ⟨170, 220, ⟨0, 2, false, true, false, 220, 220⟩⟩,
   ⟨221, 361, ⟨2, 7, false, true, false, 221, 221⟩⟩,
   ⟨362, 466, ⟨2, 7, false, false, false, 362, 362⟩⟩],
  [⟨155, 169, ⟨0, 2, true, true, false, 169, 169⟩⟩,
   ⟨170, 258, ⟨0, 2, false, true, false, 258, 258⟩⟩,
   ⟨259, 361, ⟨2, 7, false, true, false, 361, 361⟩⟩,
   ⟨362, 543, ⟨2, 7, false, false, false, 543, 543⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_221_lower : ConfigurationBounds 221 4593 119 := by
  apply configuration_of_cells 221 4593 119 data_221_lower
  decide +kernel

private def data_222_lower : Array (List Chunk) := #[
  [⟨1, 170, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨171, 182, ⟨0, 3, false, true, false, 171, 171⟩⟩,
   ⟨183, 339, ⟨3, 7, false, true, false, 183, 183⟩⟩,
   ⟨340, 390, ⟨3, 7, false, false, false, 340, 340⟩⟩],
  [⟨78, 170, ⟨0, 3, true, true, false, 170, 170⟩⟩,
   ⟨171, 221, ⟨0, 3, false, true, false, 221, 221⟩⟩,
   ⟨222, 339, ⟨3, 7, false, true, false, 222, 222⟩⟩,
   ⟨340, 429, ⟨3, 7, false, false, false, 340, 340⟩⟩],
  [⟨117, 170, ⟨0, 2, true, true, false, 170, 170⟩⟩,
   ⟨171, 221, ⟨0, 2, false, true, false, 221, 221⟩⟩,
   ⟨222, 339, ⟨2, 7, false, true, false, 222, 222⟩⟩,
   ⟨340, 468, ⟨2, 7, false, false, false, 340, 340⟩⟩],
  [⟨156, 170, ⟨0, 2, true, true, false, 170, 170⟩⟩,
   ⟨171, 260, ⟨0, 2, false, true, false, 260, 260⟩⟩,
   ⟨261, 339, ⟨2, 7, false, true, false, 339, 339⟩⟩,
   ⟨340, 545, ⟨2, 7, false, false, false, 545, 545⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_222_lower : ConfigurationBounds 222 4634 120 := by
  apply configuration_of_cells 222 4634 120 data_222_lower
  decide +kernel

private def data_223_lower : Array (List Chunk) := #[
  [⟨1, 171, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨172, 182, ⟨0, 3, false, true, false, 172, 172⟩⟩,
   ⟨183, 286, ⟨3, 7, false, true, false, 183, 183⟩⟩,
   ⟨287, 390, ⟨3, 7, false, false, false, 287, 287⟩⟩],
  [⟨79, 171, ⟨0, 3, true, true, false, 171, 171⟩⟩,
   ⟨172, 222, ⟨0, 3, false, true, false, 222, 222⟩⟩,
   ⟨223, 286, ⟨3, 7, false, true, false, 223, 223⟩⟩,
   ⟨287, 430, ⟨3, 7, false, false, false, 287, 287⟩⟩],
  [⟨118, 171, ⟨0, 2, true, true, false, 171, 171⟩⟩,
   ⟨172, 222, ⟨0, 2, false, true, false, 222, 222⟩⟩,
   ⟨223, 286, ⟨2, 7, false, true, false, 223, 223⟩⟩,
   ⟨287, 469, ⟨2, 7, false, false, false, 287, 287⟩⟩],
  [⟨158, 171, ⟨0, 2, true, true, false, 171, 171⟩⟩,
   ⟨172, 261, ⟨0, 2, false, true, false, 261, 261⟩⟩,
   ⟨262, 286, ⟨2, 7, false, true, false, 286, 286⟩⟩,
   ⟨287, 547, ⟨2, 7, false, false, false, 547, 547⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_223_lower : ConfigurationBounds 223 4675 121 := by
  apply configuration_of_cells 223 4675 121 data_223_lower
  decide +kernel

private def data_224_lower : Array (List Chunk) := #[
  [⟨1, 172, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨173, 183, ⟨0, 3, false, true, false, 173, 173⟩⟩,
   ⟨184, 368, ⟨3, 7, false, true, false, 184, 184⟩⟩,
   ⟨369, 393, ⟨3, 7, false, false, false, 369, 369⟩⟩],
  [⟨79, 172, ⟨0, 3, true, true, false, 172, 172⟩⟩,
   ⟨173, 223, ⟨0, 3, false, true, false, 223, 223⟩⟩,
   ⟨224, 368, ⟨3, 7, false, true, false, 224, 224⟩⟩,
   ⟨369, 433, ⟨3, 7, false, false, false, 369, 369⟩⟩],
  [⟨118, 172, ⟨0, 2, true, true, false, 172, 172⟩⟩,
   ⟨173, 223, ⟨0, 2, false, true, false, 223, 223⟩⟩,
   ⟨224, 368, ⟨2, 7, false, true, false, 224, 224⟩⟩,
   ⟨369, 472, ⟨2, 7, false, false, false, 369, 369⟩⟩],
  [⟨158, 172, ⟨0, 2, true, true, false, 172, 172⟩⟩,
   ⟨173, 262, ⟨0, 2, false, true, false, 262, 262⟩⟩,
   ⟨263, 368, ⟨2, 7, false, true, false, 368, 368⟩⟩,
   ⟨369, 550, ⟨2, 7, false, false, false, 550, 550⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_224_lower : ConfigurationBounds 224 4717 121 := by
  apply configuration_of_cells 224 4717 121 data_224_lower
  decide +kernel

private def data_225_lower : Array (List Chunk) := #[
  [⟨1, 172, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨173, 184, ⟨0, 3, false, true, false, 173, 173⟩⟩,
   ⟨185, 396, ⟨3, 7, false, true, false, 185, 185⟩⟩],
  [⟨79, 172, ⟨0, 3, true, true, false, 172, 172⟩⟩,
   ⟨173, 224, ⟨0, 3, false, true, false, 224, 224⟩⟩,
   ⟨225, 421, ⟨3, 7, false, true, false, 225, 225⟩⟩,
   ⟨422, 436, ⟨3, 7, false, false, false, 422, 422⟩⟩],
  [⟨118, 172, ⟨0, 2, true, true, false, 172, 172⟩⟩,
   ⟨173, 224, ⟨0, 2, false, true, false, 224, 224⟩⟩,
   ⟨225, 421, ⟨2, 7, false, true, false, 225, 225⟩⟩,
   ⟨422, 475, ⟨2, 7, false, false, false, 422, 422⟩⟩],
  [⟨158, 172, ⟨0, 2, true, true, false, 172, 172⟩⟩,
   ⟨173, 263, ⟨0, 2, false, true, false, 263, 263⟩⟩,
   ⟨264, 421, ⟨2, 7, false, true, false, 421, 421⟩⟩,
   ⟨422, 553, ⟨2, 7, false, false, false, 553, 553⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_225_lower : ConfigurationBounds 225 4759 121 := by
  apply configuration_of_cells 225 4759 121 data_225_lower
  decide +kernel

private def data_226_lower : Array (List Chunk) := #[
  [⟨1, 173, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨174, 185, ⟨0, 3, false, true, false, 174, 174⟩⟩,
   ⟨186, 399, ⟨3, 7, false, true, false, 186, 186⟩⟩],
  [⟨79, 173, ⟨0, 3, true, true, false, 173, 173⟩⟩,
   ⟨174, 225, ⟨0, 3, false, true, false, 225, 225⟩⟩,
   ⟨226, 439, ⟨3, 7, false, true, false, 226, 226⟩⟩],
  [⟨118, 173, ⟨0, 2, true, true, false, 173, 173⟩⟩,
   ⟨174, 225, ⟨0, 2, false, true, false, 225, 225⟩⟩,
   ⟨226, 443, ⟨2, 7, false, true, false, 226, 226⟩⟩,
   ⟨444, 478, ⟨2, 7, false, false, false, 444, 444⟩⟩],
  [⟨158, 173, ⟨0, 2, true, true, false, 173, 173⟩⟩,
   ⟨174, 264, ⟨0, 2, false, true, false, 264, 264⟩⟩,
   ⟨265, 443, ⟨2, 7, false, true, false, 443, 443⟩⟩,
   ⟨444, 556, ⟨2, 7, false, false, false, 556, 556⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_226_lower : ConfigurationBounds 226 4801 121 := by
  apply configuration_of_cells 226 4801 121 data_226_lower
  decide +kernel

private def data_227_lower : Array (List Chunk) := #[
  [⟨1, 174, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨175, 186, ⟨0, 3, false, true, false, 175, 175⟩⟩,
   ⟨187, 400, ⟨3, 7, false, true, false, 187, 187⟩⟩],
  [⟨80, 174, ⟨0, 3, true, true, false, 174, 174⟩⟩,
   ⟨175, 226, ⟨0, 3, false, true, false, 226, 226⟩⟩,
   ⟨227, 434, ⟨3, 7, false, true, false, 227, 227⟩⟩,
   ⟨435, 440, ⟨3, 7, false, false, false, 435, 435⟩⟩],
  [⟨119, 174, ⟨0, 2, true, true, false, 174, 174⟩⟩,
   ⟨175, 226, ⟨0, 2, false, true, false, 226, 226⟩⟩,
   ⟨227, 434, ⟨2, 7, false, true, false, 227, 227⟩⟩,
   ⟨435, 479, ⟨2, 7, false, false, false, 435, 435⟩⟩],
  [⟨159, 174, ⟨0, 2, true, true, false, 174, 174⟩⟩,
   ⟨175, 265, ⟨0, 2, false, true, false, 265, 265⟩⟩,
   ⟨266, 434, ⟨2, 7, false, true, false, 434, 434⟩⟩,
   ⟨435, 558, ⟨2, 7, false, false, false, 558, 558⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_227_lower : ConfigurationBounds 227 4843 122 := by
  apply configuration_of_cells 227 4843 122 data_227_lower
  decide +kernel

private def data_228_lower : Array (List Chunk) := #[
  [⟨1, 175, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨176, 187, ⟨0, 3, false, true, false, 176, 176⟩⟩,
   ⟨188, 394, ⟨3, 7, false, true, false, 188, 188⟩⟩,
   ⟨395, 401, ⟨3, 7, false, false, false, 395, 395⟩⟩],
  [⟨80, 175, ⟨0, 3, true, true, false, 175, 175⟩⟩,
   ⟨176, 227, ⟨0, 3, false, true, false, 227, 227⟩⟩,
   ⟨228, 394, ⟨3, 7, false, true, false, 228, 228⟩⟩,
   ⟨395, 441, ⟨3, 7, false, false, false, 395, 395⟩⟩],
  [⟨120, 175, ⟨0, 2, true, true, false, 175, 175⟩⟩,
   ⟨176, 227, ⟨0, 2, false, true, false, 227, 227⟩⟩,
   ⟨228, 394, ⟨2, 7, false, true, false, 228, 228⟩⟩,
   ⟨395, 481, ⟨2, 7, false, false, false, 395, 395⟩⟩],
  [⟨160, 175, ⟨0, 2, true, true, false, 175, 175⟩⟩,
   ⟨176, 267, ⟨0, 2, false, true, false, 267, 267⟩⟩,
   ⟨268, 394, ⟨2, 7, false, true, false, 394, 394⟩⟩,
   ⟨395, 560, ⟨2, 7, false, false, false, 560, 560⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_228_lower : ConfigurationBounds 228 4885 123 := by
  apply configuration_of_cells 228 4885 123 data_228_lower
  decide +kernel

private def data_229_lower : Array (List Chunk) := #[
  [⟨1, 176, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨177, 187, ⟨0, 3, false, true, false, 177, 177⟩⟩,
   ⟨188, 322, ⟨3, 7, false, true, false, 188, 188⟩⟩,
   ⟨323, 401, ⟨3, 7, false, false, false, 323, 323⟩⟩],
  [⟨81, 176, ⟨0, 3, true, true, false, 176, 176⟩⟩,
   ⟨177, 228, ⟨0, 3, false, true, false, 228, 228⟩⟩,
   ⟨229, 322, ⟨3, 7, false, true, false, 229, 229⟩⟩,
   ⟨323, 442, ⟨3, 7, false, false, false, 323, 323⟩⟩],
  [⟨121, 176, ⟨0, 2, true, true, false, 176, 176⟩⟩,
   ⟨177, 228, ⟨0, 2, false, true, false, 228, 228⟩⟩,
   ⟨229, 322, ⟨2, 7, false, true, false, 229, 229⟩⟩,
   ⟨323, 482, ⟨2, 7, false, false, false, 323, 323⟩⟩],
  [⟨162, 176, ⟨0, 2, true, true, false, 176, 176⟩⟩,
   ⟨177, 268, ⟨0, 2, false, true, false, 268, 268⟩⟩,
   ⟨269, 322, ⟨2, 7, false, true, false, 322, 322⟩⟩,
   ⟨323, 562, ⟨2, 7, false, false, false, 562, 562⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_229_lower : ConfigurationBounds 229 4927 124 := by
  apply configuration_of_cells 229 4927 124 data_229_lower
  decide +kernel

private def data_230_lower : Array (List Chunk) := #[
  [⟨1, 176, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨177, 188, ⟨0, 3, false, true, false, 177, 177⟩⟩,
   ⟨189, 390, ⟨3, 7, false, true, false, 189, 189⟩⟩,
   ⟨391, 404, ⟨3, 7, false, false, false, 391, 391⟩⟩],
  [⟨81, 176, ⟨0, 3, true, true, false, 176, 176⟩⟩,
   ⟨177, 229, ⟨0, 3, false, true, false, 229, 229⟩⟩,
   ⟨230, 390, ⟨3, 7, false, true, false, 230, 230⟩⟩,
   ⟨391, 445, ⟨3, 7, false, false, false, 391, 391⟩⟩],
  [⟨121, 176, ⟨0, 2, true, true, false, 176, 176⟩⟩,
   ⟨177, 229, ⟨0, 2, false, true, false, 229, 229⟩⟩,
   ⟨230, 390, ⟨2, 7, false, true, false, 230, 230⟩⟩,
   ⟨391, 485, ⟨2, 7, false, false, false, 391, 391⟩⟩],
  [⟨162, 176, ⟨0, 2, true, true, false, 176, 176⟩⟩,
   ⟨177, 269, ⟨0, 2, false, true, false, 269, 269⟩⟩,
   ⟨270, 390, ⟨2, 7, false, true, false, 390, 390⟩⟩,
   ⟨391, 565, ⟨2, 7, false, false, false, 565, 565⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_230_lower : ConfigurationBounds 230 4970 124 := by
  apply configuration_of_cells 230 4970 124 data_230_lower
  decide +kernel

private def data_231_lower : Array (List Chunk) := #[
  [⟨1, 177, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨178, 189, ⟨0, 3, false, true, false, 178, 178⟩⟩,
   ⟨190, 407, ⟨3, 7, false, true, false, 190, 190⟩⟩],
  [⟨81, 177, ⟨0, 3, true, true, false, 177, 177⟩⟩,
   ⟨178, 230, ⟨0, 3, false, true, false, 230, 230⟩⟩,
   ⟨231, 426, ⟨3, 7, false, true, false, 231, 231⟩⟩,
   ⟨427, 448, ⟨3, 7, false, false, false, 427, 427⟩⟩],
  [⟨121, 177, ⟨0, 2, true, true, false, 177, 177⟩⟩,
   ⟨178, 230, ⟨0, 2, false, true, false, 230, 230⟩⟩,
   ⟨231, 426, ⟨2, 7, false, true, false, 231, 231⟩⟩,
   ⟨427, 488, ⟨2, 7, false, false, false, 427, 427⟩⟩],
  [⟨162, 177, ⟨0, 2, true, true, false, 177, 177⟩⟩,
   ⟨178, 270, ⟨0, 2, false, true, false, 270, 270⟩⟩,
   ⟨271, 426, ⟨2, 7, false, true, false, 426, 426⟩⟩,
   ⟨427, 568, ⟨2, 7, false, false, false, 568, 568⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_231_lower : ConfigurationBounds 231 5013 124 := by
  apply configuration_of_cells 231 5013 124 data_231_lower
  decide +kernel

private def data_232_lower : Array (List Chunk) := #[
  [⟨1, 178, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨179, 190, ⟨0, 3, false, true, false, 179, 179⟩⟩,
   ⟨191, 408, ⟨3, 7, false, true, false, 191, 191⟩⟩],
  [⟨82, 178, ⟨0, 3, true, true, false, 178, 178⟩⟩,
   ⟨179, 231, ⟨0, 3, false, true, false, 231, 231⟩⟩,
   ⟨232, 432, ⟨3, 7, false, true, false, 232, 232⟩⟩,
   ⟨433, 449, ⟨3, 7, false, false, false, 433, 433⟩⟩],
  [⟨122, 178, ⟨0, 2, true, true, false, 178, 178⟩⟩,
   ⟨179, 231, ⟨0, 2, false, true, false, 231, 231⟩⟩,
   ⟨232, 432, ⟨2, 7, false, true, false, 232, 232⟩⟩,
   ⟨433, 489, ⟨2, 7, false, false, false, 433, 433⟩⟩],
  [⟨163, 178, ⟨0, 2, true, true, false, 178, 178⟩⟩,
   ⟨179, 271, ⟨0, 2, false, true, false, 271, 271⟩⟩,
   ⟨272, 432, ⟨2, 7, false, true, false, 432, 432⟩⟩,
   ⟨433, 570, ⟨2, 7, false, false, false, 570, 570⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_232_lower : ConfigurationBounds 232 5056 125 := by
  apply configuration_of_cells 232 5056 125 data_232_lower
  decide +kernel

private def data_233_lower : Array (List Chunk) := #[
  [⟨1, 178, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨179, 191, ⟨0, 3, false, true, false, 179, 179⟩⟩,
   ⟨192, 404, ⟨3, 7, false, true, false, 192, 192⟩⟩,
   ⟨405, 411, ⟨3, 7, false, false, false, 405, 405⟩⟩],
  [⟨82, 178, ⟨0, 3, true, true, false, 178, 178⟩⟩,
   ⟨179, 232, ⟨0, 3, false, true, false, 232, 232⟩⟩,
   ⟨233, 404, ⟨3, 7, false, true, false, 233, 233⟩⟩,
   ⟨405, 452, ⟨3, 7, false, false, false, 405, 405⟩⟩],
  [⟨122, 178, ⟨0, 2, true, true, false, 178, 178⟩⟩,
   ⟨179, 232, ⟨0, 2, false, true, false, 232, 232⟩⟩,
   ⟨233, 404, ⟨2, 7, false, true, false, 233, 233⟩⟩,
   ⟨405, 492, ⟨2, 7, false, false, false, 405, 405⟩⟩],
  [⟨163, 178, ⟨0, 2, true, true, false, 178, 178⟩⟩,
   ⟨179, 272, ⟨0, 2, false, true, false, 272, 272⟩⟩,
   ⟨273, 404, ⟨2, 7, false, true, false, 404, 404⟩⟩,
   ⟨405, 573, ⟨2, 7, false, false, false, 573, 573⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_233_lower : ConfigurationBounds 233 5099 125 := by
  apply configuration_of_cells 233 5099 125 data_233_lower
  decide +kernel

private def data_234_lower : Array (List Chunk) := #[
  [⟨1, 179, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨180, 192, ⟨0, 3, false, true, false, 180, 180⟩⟩,
   ⟨193, 344, ⟨3, 7, false, true, false, 193, 193⟩⟩,
   ⟨345, 412, ⟨3, 7, false, false, false, 345, 345⟩⟩],
  [⟨82, 179, ⟨0, 3, true, true, false, 179, 179⟩⟩,
   ⟨180, 233, ⟨0, 3, false, true, false, 233, 233⟩⟩,
   ⟨234, 344, ⟨3, 7, false, true, false, 234, 234⟩⟩,
   ⟨345, 453, ⟨3, 7, false, false, false, 345, 345⟩⟩],
  [⟨123, 179, ⟨0, 2, true, true, false, 179, 179⟩⟩,
   ⟨180, 233, ⟨0, 2, false, true, false, 233, 233⟩⟩,
   ⟨234, 344, ⟨2, 7, false, true, false, 234, 234⟩⟩,
   ⟨345, 494, ⟨2, 7, false, false, false, 345, 345⟩⟩],
  [⟨164, 179, ⟨0, 2, true, true, false, 179, 179⟩⟩,
   ⟨180, 274, ⟨0, 2, false, true, false, 274, 274⟩⟩,
   ⟨275, 344, ⟨2, 7, false, true, false, 344, 344⟩⟩,
   ⟨345, 575, ⟨2, 7, false, false, false, 575, 575⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_234_lower : ConfigurationBounds 234 5142 126 := by
  apply configuration_of_cells 234 5142 126 data_234_lower
  decide +kernel

private def data_235_lower : Array (List Chunk) := #[
  [⟨1, 180, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨181, 193, ⟨0, 3, false, true, false, 181, 181⟩⟩,
   ⟨194, 415, ⟨3, 7, false, true, false, 194, 194⟩⟩],
  [⟨82, 180, ⟨0, 3, true, true, false, 180, 180⟩⟩,
   ⟨181, 234, ⟨0, 3, false, true, false, 234, 234⟩⟩,
   ⟨235, 429, ⟨3, 7, false, true, false, 235, 235⟩⟩,
   ⟨430, 456, ⟨3, 7, false, false, false, 430, 430⟩⟩],
  [⟨123, 180, ⟨0, 2, true, true, false, 180, 180⟩⟩,
   ⟨181, 234, ⟨0, 2, false, true, false, 234, 234⟩⟩,
   ⟨235, 429, ⟨2, 7, false, true, false, 235, 235⟩⟩,
   ⟨430, 497, ⟨2, 7, false, false, false, 430, 430⟩⟩],
  [⟨164, 180, ⟨0, 2, true, true, false, 180, 180⟩⟩,
   ⟨181, 275, ⟨0, 2, false, true, false, 275, 275⟩⟩,
   ⟨276, 429, ⟨2, 7, false, true, false, 429, 429⟩⟩,
   ⟨430, 578, ⟨2, 7, false, false, false, 578, 578⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_235_lower : ConfigurationBounds 235 5186 126 := by
  apply configuration_of_cells 235 5186 126 data_235_lower
  decide +kernel

private def data_236_lower : Array (List Chunk) := #[
  [⟨1, 181, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨182, 193, ⟨0, 3, false, true, false, 182, 182⟩⟩,
   ⟨194, 305, ⟨3, 7, false, true, false, 194, 194⟩⟩,
   ⟨306, 413, ⟨3, 7, false, false, false, 306, 306⟩⟩],
  [⟨84, 181, ⟨0, 3, true, true, false, 181, 181⟩⟩,
   ⟨182, 235, ⟨0, 3, false, true, false, 235, 235⟩⟩,
   ⟨236, 305, ⟨3, 7, false, true, false, 236, 236⟩⟩,
   ⟨306, 455, ⟨3, 7, false, false, false, 306, 306⟩⟩],
  [⟨125, 181, ⟨0, 2, true, true, false, 181, 181⟩⟩,
   ⟨182, 235, ⟨0, 2, false, true, false, 235, 235⟩⟩,
   ⟨236, 305, ⟨2, 7, false, true, false, 236, 236⟩⟩,
   ⟨306, 496, ⟨2, 7, false, false, false, 306, 306⟩⟩],
  [⟨167, 181, ⟨0, 2, true, true, false, 181, 181⟩⟩,
   ⟨182, 276, ⟨0, 2, false, true, false, 276, 276⟩⟩,
   ⟨277, 305, ⟨2, 7, false, true, false, 305, 305⟩⟩,
   ⟨306, 579, ⟨2, 7, false, false, false, 579, 579⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_236_lower : ConfigurationBounds 236 5229 128 := by
  apply configuration_of_cells 236 5229 128 data_236_lower
  decide +kernel

private def data_237_lower : Array (List Chunk) := #[
  [⟨1, 182, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨183, 194, ⟨0, 3, false, true, false, 183, 183⟩⟩,
   ⟨195, 324, ⟨3, 7, false, true, false, 195, 195⟩⟩,
   ⟨325, 416, ⟨3, 7, false, false, false, 325, 325⟩⟩],
  [⟨84, 182, ⟨0, 3, true, true, false, 182, 182⟩⟩,
   ⟨183, 236, ⟨0, 3, false, true, false, 236, 236⟩⟩,
   ⟨237, 324, ⟨3, 7, false, true, false, 237, 237⟩⟩,
   ⟨325, 458, ⟨3, 7, false, false, false, 325, 325⟩⟩],
  [⟨125, 182, ⟨0, 2, true, true, false, 182, 182⟩⟩,
   ⟨183, 236, ⟨0, 2, false, true, false, 236, 236⟩⟩,
   ⟨237, 324, ⟨2, 7, false, true, false, 237, 237⟩⟩,
   ⟨325, 499, ⟨2, 7, false, false, false, 325, 325⟩⟩],
  [⟨167, 182, ⟨0, 2, true, true, false, 182, 182⟩⟩,
   ⟨183, 277, ⟨0, 2, false, true, false, 277, 277⟩⟩,
   ⟨278, 324, ⟨2, 7, false, true, false, 324, 324⟩⟩,
   ⟨325, 582, ⟨2, 7, false, false, false, 582, 582⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_237_lower : ConfigurationBounds 237 5273 128 := by
  apply configuration_of_cells 237 5273 128 data_237_lower
  decide +kernel

private def data_238_lower : Array (List Chunk) := #[
  [⟨1, 183, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨184, 195, ⟨0, 3, false, true, false, 184, 184⟩⟩,
   ⟨196, 311, ⟨3, 7, false, true, false, 196, 196⟩⟩,
   ⟨312, 417, ⟨3, 7, false, false, false, 312, 312⟩⟩],
  [⟨84, 183, ⟨0, 3, true, true, false, 183, 183⟩⟩,
   ⟨184, 237, ⟨0, 3, false, true, false, 237, 237⟩⟩,
   ⟨238, 311, ⟨3, 7, false, true, false, 238, 238⟩⟩,
   ⟨312, 459, ⟨3, 7, false, false, false, 312, 312⟩⟩],
  [⟨126, 183, ⟨0, 2, true, true, false, 183, 183⟩⟩,
   ⟨184, 237, ⟨0, 2, false, true, false, 237, 237⟩⟩,
   ⟨238, 311, ⟨2, 7, false, true, false, 238, 238⟩⟩,
   ⟨312, 501, ⟨2, 7, false, false, false, 312, 312⟩⟩],
  [⟨168, 183, ⟨0, 2, true, true, false, 183, 183⟩⟩,
   ⟨184, 279, ⟨0, 2, false, true, false, 279, 279⟩⟩,
   ⟨280, 311, ⟨2, 7, false, true, false, 311, 311⟩⟩,
   ⟨312, 584, ⟨2, 7, false, false, false, 584, 584⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_238_lower : ConfigurationBounds 238 5317 129 := by
  apply configuration_of_cells 238 5317 129 data_238_lower
  decide +kernel

private def data_239_lower : Array (List Chunk) := #[
  [⟨1, 183, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨184, 196, ⟨0, 3, false, true, false, 184, 184⟩⟩,
   ⟨197, 420, ⟨3, 7, false, true, false, 197, 197⟩⟩],
  [⟨84, 183, ⟨0, 3, true, true, false, 183, 183⟩⟩,
   ⟨184, 238, ⟨0, 3, false, true, false, 238, 238⟩⟩,
   ⟨239, 444, ⟨3, 7, false, true, false, 239, 239⟩⟩,
   ⟨445, 462, ⟨3, 7, false, false, false, 445, 445⟩⟩],
  [⟨126, 183, ⟨0, 2, true, true, false, 183, 183⟩⟩,
   ⟨184, 238, ⟨0, 2, false, true, false, 238, 238⟩⟩,
   ⟨239, 444, ⟨2, 7, false, true, false, 239, 239⟩⟩,
   ⟨445, 504, ⟨2, 7, false, false, false, 445, 445⟩⟩],
  [⟨168, 183, ⟨0, 2, true, true, false, 183, 183⟩⟩,
   ⟨184, 280, ⟨0, 2, false, true, false, 280, 280⟩⟩,
   ⟨281, 444, ⟨2, 7, false, true, false, 444, 444⟩⟩,
   ⟨445, 587, ⟨2, 7, false, false, false, 587, 587⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_239_lower : ConfigurationBounds 239 5362 129 := by
  apply configuration_of_cells 239 5362 129 data_239_lower
  decide +kernel

private def data_240_lower : Array (List Chunk) := #[
  [⟨1, 184, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨185, 196, ⟨0, 3, false, true, false, 185, 185⟩⟩,
   ⟨197, 365, ⟨3, 7, false, true, false, 197, 197⟩⟩,
   ⟨366, 420, ⟨3, 7, false, false, false, 366, 366⟩⟩],
  [⟨85, 184, ⟨0, 3, true, true, false, 184, 184⟩⟩,
   ⟨185, 239, ⟨0, 3, false, true, false, 239, 239⟩⟩,
   ⟨240, 365, ⟨3, 7, false, true, false, 240, 240⟩⟩,
   ⟨366, 463, ⟨3, 7, false, false, false, 366, 366⟩⟩],
  [⟨127, 184, ⟨0, 2, true, true, false, 184, 184⟩⟩,
   ⟨185, 239, ⟨0, 2, false, true, false, 239, 239⟩⟩,
   ⟨240, 365, ⟨2, 7, false, true, false, 240, 240⟩⟩,
   ⟨366, 505, ⟨2, 7, false, false, false, 366, 366⟩⟩],
  [⟨170, 184, ⟨0, 2, true, true, false, 184, 184⟩⟩,
   ⟨185, 281, ⟨0, 2, false, true, false, 281, 281⟩⟩,
   ⟨282, 365, ⟨2, 7, false, true, false, 365, 365⟩⟩,
   ⟨366, 589, ⟨2, 7, false, false, false, 589, 589⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_240_lower : ConfigurationBounds 240 5406 130 := by
  apply configuration_of_cells 240 5406 130 data_240_lower
  decide +kernel

private def data_241_lower : Array (List Chunk) := #[
  [⟨1, 185, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨186, 197, ⟨0, 3, false, true, false, 186, 186⟩⟩,
   ⟨198, 423, ⟨3, 7, false, true, false, 198, 198⟩⟩],
  [⟨85, 185, ⟨0, 3, true, true, false, 185, 185⟩⟩,
   ⟨186, 240, ⟨0, 3, false, true, false, 240, 240⟩⟩,
   ⟨241, 433, ⟨3, 7, false, true, false, 241, 241⟩⟩,
   ⟨434, 466, ⟨3, 7, false, false, false, 434, 434⟩⟩],
  [⟨127, 185, ⟨0, 2, true, true, false, 185, 185⟩⟩,
   ⟨186, 240, ⟨0, 2, false, true, false, 240, 240⟩⟩,
   ⟨241, 433, ⟨2, 7, false, true, false, 241, 241⟩⟩,
   ⟨434, 508, ⟨2, 7, false, false, false, 434, 434⟩⟩],
  [⟨170, 185, ⟨0, 2, true, true, false, 185, 185⟩⟩,
   ⟨186, 282, ⟨0, 2, false, true, false, 282, 282⟩⟩,
   ⟨283, 433, ⟨2, 7, false, true, false, 433, 433⟩⟩,
   ⟨434, 592, ⟨2, 7, false, false, false, 592, 592⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_241_lower : ConfigurationBounds 241 5451 130 := by
  apply configuration_of_cells 241 5451 130 data_241_lower
  decide +kernel

private def data_242_lower : Array (List Chunk) := #[
  [⟨1, 185, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨186, 198, ⟨0, 3, false, true, false, 186, 186⟩⟩,
   ⟨199, 426, ⟨3, 7, false, true, false, 199, 199⟩⟩],
  [⟨85, 185, ⟨0, 3, true, true, false, 185, 185⟩⟩,
   ⟨186, 241, ⟨0, 3, false, true, false, 241, 241⟩⟩,
   ⟨242, 468, ⟨3, 7, false, true, false, 242, 242⟩⟩,
   ⟨469, 469, ⟨3, 7, false, false, false, 469, 469⟩⟩],
  [⟨127, 185, ⟨0, 2, true, true, false, 185, 185⟩⟩,
   ⟨186, 241, ⟨0, 2, false, true, false, 241, 241⟩⟩,
   ⟨242, 468, ⟨2, 7, false, true, false, 242, 242⟩⟩,
   ⟨469, 511, ⟨2, 7, false, false, false, 469, 469⟩⟩],
  [⟨170, 185, ⟨0, 2, true, true, false, 185, 185⟩⟩,
   ⟨186, 283, ⟨0, 2, false, true, false, 283, 283⟩⟩,
   ⟨284, 468, ⟨2, 7, false, true, false, 468, 468⟩⟩,
   ⟨469, 595, ⟨2, 7, false, false, false, 595, 595⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_242_lower : ConfigurationBounds 242 5496 130 := by
  apply configuration_of_cells 242 5496 130 data_242_lower
  decide +kernel

private def data_243_lower : Array (List Chunk) := #[
  [⟨1, 186, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨187, 199, ⟨0, 3, false, true, false, 187, 187⟩⟩,
   ⟨200, 427, ⟨3, 7, false, true, false, 200, 200⟩⟩],
  [⟨86, 186, ⟨0, 3, true, true, false, 186, 186⟩⟩,
   ⟨187, 242, ⟨0, 3, false, true, false, 242, 242⟩⟩,
   ⟨243, 470, ⟨3, 7, false, true, false, 243, 243⟩⟩],
  [⟨128, 186, ⟨0, 2, true, true, false, 186, 186⟩⟩,
   ⟨187, 242, ⟨0, 2, false, true, false, 242, 242⟩⟩,
   ⟨243, 470, ⟨2, 7, false, true, false, 243, 243⟩⟩,
   ⟨471, 512, ⟨2, 7, false, false, false, 471, 471⟩⟩],
  [⟨171, 186, ⟨0, 2, true, true, false, 186, 186⟩⟩,
   ⟨187, 284, ⟨0, 2, false, true, false, 284, 284⟩⟩,
   ⟨285, 470, ⟨2, 7, false, true, false, 470, 470⟩⟩,
   ⟨471, 597, ⟨2, 7, false, false, false, 597, 597⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_243_lower : ConfigurationBounds 243 5541 131 := by
  apply configuration_of_cells 243 5541 131 data_243_lower
  decide +kernel

private def data_244_lower : Array (List Chunk) := #[
  [⟨1, 187, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨188, 200, ⟨0, 3, false, true, false, 188, 188⟩⟩,
   ⟨201, 430, ⟨3, 7, false, true, false, 201, 201⟩⟩],
  [⟨86, 187, ⟨0, 3, true, true, false, 187, 187⟩⟩,
   ⟨188, 243, ⟨0, 3, false, true, false, 243, 243⟩⟩,
   ⟨244, 438, ⟨3, 7, false, true, false, 244, 244⟩⟩,
   ⟨439, 473, ⟨3, 7, false, false, false, 439, 439⟩⟩],
  [⟨128, 187, ⟨0, 2, true, true, false, 187, 187⟩⟩,
   ⟨188, 243, ⟨0, 2, false, true, false, 243, 243⟩⟩,
   ⟨244, 438, ⟨2, 7, false, true, false, 244, 244⟩⟩,
   ⟨439, 515, ⟨2, 7, false, false, false, 439, 439⟩⟩],
  [⟨171, 187, ⟨0, 2, true, true, false, 187, 187⟩⟩,
   ⟨188, 285, ⟨0, 2, false, true, false, 285, 285⟩⟩,
   ⟨286, 438, ⟨2, 7, false, true, false, 438, 438⟩⟩,
   ⟨439, 600, ⟨2, 7, false, false, false, 600, 600⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_244_lower : ConfigurationBounds 244 5586 131 := by
  apply configuration_of_cells 244 5586 131 data_244_lower
  decide +kernel

private def data_245_lower : Array (List Chunk) := #[
  [⟨1, 188, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨189, 201, ⟨0, 3, false, true, false, 189, 189⟩⟩,
   ⟨202, 372, ⟨3, 7, false, true, false, 202, 202⟩⟩,
   ⟨373, 431, ⟨3, 7, false, false, false, 373, 373⟩⟩],
  [⟨86, 188, ⟨0, 3, true, true, false, 188, 188⟩⟩,
   ⟨189, 244, ⟨0, 3, false, true, false, 244, 244⟩⟩,
   ⟨245, 372, ⟨3, 7, false, true, false, 245, 245⟩⟩,
   ⟨373, 474, ⟨3, 7, false, false, false, 373, 373⟩⟩],
  [⟨129, 188, ⟨0, 2, true, true, false, 188, 188⟩⟩,
   ⟨189, 244, ⟨0, 2, false, true, false, 244, 244⟩⟩,
   ⟨245, 372, ⟨2, 7, false, true, false, 245, 245⟩⟩,
   ⟨373, 517, ⟨2, 7, false, false, false, 373, 373⟩⟩],
  [⟨172, 188, ⟨0, 2, true, true, false, 188, 188⟩⟩,
   ⟨189, 287, ⟨0, 2, false, true, false, 287, 287⟩⟩,
   ⟨288, 372, ⟨2, 7, false, true, false, 372, 372⟩⟩,
   ⟨373, 602, ⟨2, 7, false, false, false, 602, 602⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_245_lower : ConfigurationBounds 245 5631 132 := by
  apply configuration_of_cells 245 5631 132 data_245_lower
  decide +kernel

private def data_246_lower : Array (List Chunk) := #[
  [⟨1, 188, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨189, 202, ⟨0, 3, false, true, false, 189, 189⟩⟩,
   ⟨203, 434, ⟨3, 7, false, true, false, 203, 203⟩⟩],
  [⟨86, 188, ⟨0, 3, true, true, false, 188, 188⟩⟩,
   ⟨189, 245, ⟨0, 3, false, true, false, 245, 245⟩⟩,
   ⟨246, 457, ⟨3, 7, false, true, false, 246, 246⟩⟩,
   ⟨458, 477, ⟨3, 7, false, false, false, 458, 458⟩⟩],
  [⟨129, 188, ⟨0, 2, true, true, false, 188, 188⟩⟩,
   ⟨189, 245, ⟨0, 2, false, true, false, 245, 245⟩⟩,
   ⟨246, 457, ⟨2, 7, false, true, false, 246, 246⟩⟩,
   ⟨458, 520, ⟨2, 7, false, false, false, 458, 458⟩⟩],
  [⟨172, 188, ⟨0, 2, true, true, false, 188, 188⟩⟩,
   ⟨189, 288, ⟨0, 2, false, true, false, 288, 288⟩⟩,
   ⟨289, 457, ⟨2, 7, false, true, false, 457, 457⟩⟩,
   ⟨458, 605, ⟨2, 7, false, false, false, 605, 605⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_246_lower : ConfigurationBounds 246 5677 132 := by
  apply configuration_of_cells 246 5677 132 data_246_lower
  decide +kernel

private def data_247_lower : Array (List Chunk) := #[
  [⟨1, 190, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨191, 202, ⟨0, 3, false, true, false, 191, 191⟩⟩,
   ⟨203, 324, ⟨3, 7, false, true, false, 203, 203⟩⟩,
   ⟨325, 432, ⟨3, 7, false, false, false, 325, 325⟩⟩],
  [⟨88, 190, ⟨0, 3, true, true, false, 190, 190⟩⟩,
   ⟨191, 246, ⟨0, 3, false, true, false, 246, 246⟩⟩,
   ⟨247, 324, ⟨3, 7, false, true, false, 247, 247⟩⟩,
   ⟨325, 476, ⟨3, 7, false, false, false, 325, 325⟩⟩],
  [⟨131, 190, ⟨0, 2, true, true, false, 190, 190⟩⟩,
   ⟨191, 246, ⟨0, 2, false, true, false, 246, 246⟩⟩,
   ⟨247, 324, ⟨2, 7, false, true, false, 247, 247⟩⟩,
   ⟨325, 519, ⟨2, 7, false, false, false, 325, 325⟩⟩],
  [⟨175, 190, ⟨0, 2, true, true, false, 190, 190⟩⟩,
   ⟨191, 289, ⟨0, 2, false, true, false, 289, 289⟩⟩,
   ⟨290, 324, ⟨2, 7, false, true, false, 324, 324⟩⟩,
   ⟨325, 606, ⟨2, 7, false, false, false, 606, 606⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_247_lower : ConfigurationBounds 247 5722 134 := by
  apply configuration_of_cells 247 5722 134 data_247_lower
  decide +kernel

private def data_248_lower : Array (List Chunk) := #[
  [⟨1, 190, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨191, 203, ⟨0, 3, false, true, false, 191, 191⟩⟩,
   ⟨204, 340, ⟨3, 7, false, true, false, 204, 204⟩⟩,
   ⟨341, 435, ⟨3, 7, false, false, false, 341, 341⟩⟩],
  [⟨88, 190, ⟨0, 3, true, true, false, 190, 190⟩⟩,
   ⟨191, 247, ⟨0, 3, false, true, false, 247, 247⟩⟩,
   ⟨248, 340, ⟨3, 7, false, true, false, 248, 248⟩⟩,
   ⟨341, 479, ⟨3, 7, false, false, false, 341, 341⟩⟩],
  [⟨131, 190, ⟨0, 2, true, true, false, 190, 190⟩⟩,
   ⟨191, 247, ⟨0, 2, false, true, false, 247, 247⟩⟩,
   ⟨248, 340, ⟨2, 7, false, true, false, 248, 248⟩⟩,
   ⟨341, 522, ⟨2, 7, false, false, false, 341, 341⟩⟩],
  [⟨175, 190, ⟨0, 2, true, true, false, 190, 190⟩⟩,
   ⟨191, 290, ⟨0, 2, false, true, false, 290, 290⟩⟩,
   ⟨291, 340, ⟨2, 7, false, true, false, 340, 340⟩⟩,
   ⟨341, 609, ⟨2, 7, false, false, false, 609, 609⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_248_lower : ConfigurationBounds 248 5768 134 := by
  apply configuration_of_cells 248 5768 134 data_248_lower
  decide +kernel

private def data_249_lower : Array (List Chunk) := #[
  [⟨1, 191, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨192, 204, ⟨0, 3, false, true, false, 192, 192⟩⟩,
   ⟨205, 323, ⟨3, 7, false, true, false, 205, 205⟩⟩,
   ⟨324, 436, ⟨3, 7, false, false, false, 324, 324⟩⟩],
  [⟨88, 191, ⟨0, 3, true, true, false, 191, 191⟩⟩,
   ⟨192, 248, ⟨0, 3, false, true, false, 248, 248⟩⟩,
   ⟨249, 323, ⟨3, 7, false, true, false, 249, 249⟩⟩,
   ⟨324, 480, ⟨3, 7, false, false, false, 324, 324⟩⟩],
  [⟨132, 191, ⟨0, 2, true, true, false, 191, 191⟩⟩,
   ⟨192, 248, ⟨0, 2, false, true, false, 248, 248⟩⟩,
   ⟨249, 323, ⟨2, 7, false, true, false, 249, 249⟩⟩,
   ⟨324, 524, ⟨2, 7, false, false, false, 324, 324⟩⟩],
  [⟨176, 191, ⟨0, 2, true, true, false, 191, 191⟩⟩,
   ⟨192, 292, ⟨0, 2, false, true, false, 292, 292⟩⟩,
   ⟨293, 323, ⟨2, 7, false, true, false, 323, 323⟩⟩,
   ⟨324, 611, ⟨2, 7, false, false, false, 611, 611⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_249_lower : ConfigurationBounds 249 5814 135 := by
  apply configuration_of_cells 249 5814 135 data_249_lower
  decide +kernel

private def data_250_lower : Array (List Chunk) := #[
  [⟨1, 192, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨193, 205, ⟨0, 3, false, true, false, 193, 193⟩⟩,
   ⟨206, 439, ⟨3, 7, false, true, false, 206, 206⟩⟩],
  [⟨88, 192, ⟨0, 3, true, true, false, 192, 192⟩⟩,
   ⟨193, 249, ⟨0, 3, false, true, false, 249, 249⟩⟩,
   ⟨250, 458, ⟨3, 7, false, true, false, 250, 250⟩⟩,
   ⟨459, 483, ⟨3, 7, false, false, false, 459, 459⟩⟩],
  [⟨132, 192, ⟨0, 2, true, true, false, 192, 192⟩⟩,
   ⟨193, 249, ⟨0, 2, false, true, false, 249, 249⟩⟩,
   ⟨250, 458, ⟨2, 7, false, true, false, 250, 250⟩⟩,
   ⟨459, 527, ⟨2, 7, false, false, false, 459, 459⟩⟩],
  [⟨176, 192, ⟨0, 2, true, true, false, 192, 192⟩⟩,
   ⟨193, 293, ⟨0, 2, false, true, false, 293, 293⟩⟩,
   ⟨294, 458, ⟨2, 7, false, true, false, 458, 458⟩⟩,
   ⟨459, 614, ⟨2, 7, false, false, false, 614, 614⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_250_lower : ConfigurationBounds 250 5861 135 := by
  apply configuration_of_cells 250 5861 135 data_250_lower
  decide +kernel

private def data_251_lower : Array (List Chunk) := #[
  [⟨1, 193, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨194, 205, ⟨0, 3, false, true, false, 194, 194⟩⟩,
   ⟨206, 372, ⟨3, 7, false, true, false, 206, 206⟩⟩,
   ⟨373, 439, ⟨3, 7, false, false, false, 373, 373⟩⟩],
  [⟨89, 193, ⟨0, 3, true, true, false, 193, 193⟩⟩,
   ⟨194, 250, ⟨0, 3, false, true, false, 250, 250⟩⟩,
   ⟨251, 372, ⟨3, 7, false, true, false, 251, 251⟩⟩,
   ⟨373, 484, ⟨3, 7, false, false, false, 373, 373⟩⟩],
  [⟨133, 193, ⟨0, 2, true, true, false, 193, 193⟩⟩,
   ⟨194, 250, ⟨0, 2, false, true, false, 250, 250⟩⟩,
   ⟨251, 372, ⟨2, 7, false, true, false, 251, 251⟩⟩,
   ⟨373, 528, ⟨2, 7, false, false, false, 373, 373⟩⟩],
  [⟨178, 193, ⟨0, 2, true, true, false, 193, 193⟩⟩,
   ⟨194, 294, ⟨0, 2, false, true, false, 294, 294⟩⟩,
   ⟨295, 372, ⟨2, 7, false, true, false, 372, 372⟩⟩,
   ⟨373, 616, ⟨2, 7, false, false, false, 616, 616⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_251_lower : ConfigurationBounds 251 5907 136 := by
  apply configuration_of_cells 251 5907 136 data_251_lower
  decide +kernel

private def data_252_lower : Array (List Chunk) := #[
  [⟨1, 193, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨194, 206, ⟨0, 3, false, true, false, 194, 194⟩⟩,
   ⟨207, 439, ⟨3, 7, false, true, false, 207, 207⟩⟩,
   ⟨440, 442, ⟨3, 7, false, false, false, 440, 440⟩⟩],
  [⟨89, 193, ⟨0, 3, true, true, false, 193, 193⟩⟩,
   ⟨194, 251, ⟨0, 3, false, true, false, 251, 251⟩⟩,
   ⟨252, 439, ⟨3, 7, false, true, false, 252, 252⟩⟩,
   ⟨440, 487, ⟨3, 7, false, false, false, 440, 440⟩⟩],
  [⟨133, 193, ⟨0, 2, true, true, false, 193, 193⟩⟩,
   ⟨194, 251, ⟨0, 2, false, true, false, 251, 251⟩⟩,
   ⟨252, 439, ⟨2, 7, false, true, false, 252, 252⟩⟩,
   ⟨440, 531, ⟨2, 7, false, false, false, 440, 440⟩⟩],
  [⟨178, 193, ⟨0, 2, true, true, false, 193, 193⟩⟩,
   ⟨194, 295, ⟨0, 2, false, true, false, 295, 295⟩⟩,
   ⟨296, 439, ⟨2, 7, false, true, false, 439, 439⟩⟩,
   ⟨440, 619, ⟨2, 7, false, false, false, 619, 619⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_252_lower : ConfigurationBounds 252 5954 136 := by
  apply configuration_of_cells 252 5954 136 data_252_lower
  decide +kernel

private def data_253_lower : Array (List Chunk) := #[
  [⟨1, 194, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨195, 207, ⟨0, 3, false, true, false, 195, 195⟩⟩,
   ⟨208, 445, ⟨3, 7, false, true, false, 208, 208⟩⟩],
  [⟨89, 194, ⟨0, 3, true, true, false, 194, 194⟩⟩,
   ⟨195, 252, ⟨0, 3, false, true, false, 252, 252⟩⟩,
   ⟨253, 472, ⟨3, 7, false, true, false, 253, 253⟩⟩,
   ⟨473, 490, ⟨3, 7, false, false, false, 473, 473⟩⟩],
  [⟨133, 194, ⟨0, 2, true, true, false, 194, 194⟩⟩,
   ⟨195, 252, ⟨0, 2, false, true, false, 252, 252⟩⟩,
   ⟨253, 472, ⟨2, 7, false, true, false, 253, 253⟩⟩,
   ⟨473, 534, ⟨2, 7, false, false, false, 473, 473⟩⟩],
  [⟨178, 194, ⟨0, 2, true, true, false, 194, 194⟩⟩,
   ⟨195, 296, ⟨0, 2, false, true, false, 296, 296⟩⟩,
   ⟨297, 472, ⟨2, 7, false, true, false, 472, 472⟩⟩,
   ⟨473, 622, ⟨2, 7, false, false, false, 622, 622⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_253_lower : ConfigurationBounds 253 6001 136 := by
  apply configuration_of_cells 253 6001 136 data_253_lower
  decide +kernel

private def data_254_lower : Array (List Chunk) := #[
  [⟨1, 195, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨196, 208, ⟨0, 3, false, true, false, 196, 196⟩⟩,
   ⟨209, 446, ⟨3, 7, false, true, false, 209, 209⟩⟩],
  [⟨90, 195, ⟨0, 3, true, true, false, 195, 195⟩⟩,
   ⟨196, 253, ⟨0, 3, false, true, false, 253, 253⟩⟩,
   ⟨254, 471, ⟨3, 7, false, true, false, 254, 254⟩⟩,
   ⟨472, 491, ⟨3, 7, false, false, false, 472, 472⟩⟩],
  [⟨134, 195, ⟨0, 2, true, true, false, 195, 195⟩⟩,
   ⟨196, 253, ⟨0, 2, false, true, false, 253, 253⟩⟩,
   ⟨254, 471, ⟨2, 7, false, true, false, 254, 254⟩⟩,
   ⟨472, 535, ⟨2, 7, false, false, false, 472, 472⟩⟩],
  [⟨179, 195, ⟨0, 2, true, true, false, 195, 195⟩⟩,
   ⟨196, 297, ⟨0, 2, false, true, false, 297, 297⟩⟩,
   ⟨298, 471, ⟨2, 7, false, true, false, 471, 471⟩⟩,
   ⟨472, 624, ⟨2, 7, false, false, false, 624, 624⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_254_lower : ConfigurationBounds 254 6048 137 := by
  apply configuration_of_cells 254 6048 137 data_254_lower
  decide +kernel

private def data_255_lower : Array (List Chunk) := #[
  [⟨1, 196, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨197, 209, ⟨0, 3, false, true, false, 197, 197⟩⟩,
   ⟨210, 435, ⟨3, 7, false, true, false, 210, 210⟩⟩,
   ⟨436, 447, ⟨3, 7, false, false, false, 436, 436⟩⟩],
  [⟨90, 196, ⟨0, 3, true, true, false, 196, 196⟩⟩,
   ⟨197, 254, ⟨0, 3, false, true, false, 254, 254⟩⟩,
   ⟨255, 435, ⟨3, 7, false, true, false, 255, 255⟩⟩,
   ⟨436, 492, ⟨3, 7, false, false, false, 436, 436⟩⟩],
  [⟨135, 196, ⟨0, 2, true, true, false, 196, 196⟩⟩,
   ⟨197, 254, ⟨0, 2, false, true, false, 254, 254⟩⟩,
   ⟨255, 435, ⟨2, 7, false, true, false, 255, 255⟩⟩,
   ⟨436, 537, ⟨2, 7, false, false, false, 436, 436⟩⟩],
  [⟨180, 196, ⟨0, 2, true, true, false, 196, 196⟩⟩,
   ⟨197, 299, ⟨0, 2, false, true, false, 299, 299⟩⟩,
   ⟨300, 435, ⟨2, 7, false, true, false, 435, 435⟩⟩,
   ⟨436, 626, ⟨2, 7, false, false, false, 626, 626⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_255_lower : ConfigurationBounds 255 6095 138 := by
  apply configuration_of_cells 255 6095 138 data_255_lower
  decide +kernel

private def data_256_lower : Array (List Chunk) := #[
  [⟨1, 197, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨198, 209, ⟨0, 3, false, true, false, 198, 198⟩⟩,
   ⟨210, 363, ⟨3, 7, false, true, false, 210, 210⟩⟩,
   ⟨364, 447, ⟨3, 7, false, false, false, 364, 364⟩⟩],
  [⟨91, 197, ⟨0, 3, true, true, false, 197, 197⟩⟩,
   ⟨198, 255, ⟨0, 3, false, true, false, 255, 255⟩⟩,
   ⟨256, 363, ⟨3, 7, false, true, false, 256, 256⟩⟩,
   ⟨364, 493, ⟨3, 7, false, false, false, 364, 364⟩⟩],
  [⟨136, 197, ⟨0, 2, true, true, false, 197, 197⟩⟩,
   ⟨198, 255, ⟨0, 2, false, true, false, 255, 255⟩⟩,
   ⟨256, 363, ⟨2, 7, false, true, false, 256, 256⟩⟩,
   ⟨364, 538, ⟨2, 7, false, false, false, 364, 364⟩⟩],
  [⟨182, 197, ⟨0, 2, true, true, false, 197, 197⟩⟩,
   ⟨198, 300, ⟨0, 2, false, true, false, 300, 300⟩⟩,
   ⟨301, 363, ⟨2, 7, false, true, false, 363, 363⟩⟩,
   ⟨364, 628, ⟨2, 7, false, false, false, 628, 628⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_256_lower : ConfigurationBounds 256 6142 139 := by
  apply configuration_of_cells 256 6142 139 data_256_lower
  decide +kernel

private def data_257_lower : Array (List Chunk) := #[
  [⟨1, 197, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨198, 210, ⟨0, 3, false, true, false, 198, 198⟩⟩,
   ⟨211, 447, ⟨3, 7, false, true, false, 211, 211⟩⟩,
   ⟨448, 450, ⟨3, 7, false, false, false, 448, 448⟩⟩],
  [⟨91, 197, ⟨0, 3, true, true, false, 197, 197⟩⟩,
   ⟨198, 256, ⟨0, 3, false, true, false, 256, 256⟩⟩,
   ⟨257, 447, ⟨3, 7, false, true, false, 257, 257⟩⟩,
   ⟨448, 496, ⟨3, 7, false, false, false, 448, 448⟩⟩],
  [⟨136, 197, ⟨0, 2, true, true, false, 197, 197⟩⟩,
   ⟨198, 256, ⟨0, 2, false, true, false, 256, 256⟩⟩,
   ⟨257, 447, ⟨2, 7, false, true, false, 257, 257⟩⟩,
   ⟨448, 541, ⟨2, 7, false, false, false, 448, 448⟩⟩],
  [⟨182, 197, ⟨0, 2, true, true, false, 197, 197⟩⟩,
   ⟨198, 301, ⟨0, 2, false, true, false, 301, 301⟩⟩,
   ⟨302, 447, ⟨2, 7, false, true, false, 447, 447⟩⟩,
   ⟨448, 631, ⟨2, 7, false, false, false, 631, 631⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_257_lower : ConfigurationBounds 257 6190 139 := by
  apply configuration_of_cells 257 6190 139 data_257_lower
  decide +kernel

private def data_258_lower : Array (List Chunk) := #[
  [⟨1, 198, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨199, 211, ⟨0, 3, false, true, false, 199, 199⟩⟩,
   ⟨212, 453, ⟨3, 7, false, true, false, 212, 212⟩⟩],
  [⟨91, 198, ⟨0, 3, true, true, false, 198, 198⟩⟩,
   ⟨199, 257, ⟨0, 3, false, true, false, 257, 257⟩⟩,
   ⟨258, 496, ⟨3, 7, false, true, false, 258, 258⟩⟩,
   ⟨497, 499, ⟨3, 7, false, false, false, 497, 497⟩⟩],
  [⟨136, 198, ⟨0, 2, true, true, false, 198, 198⟩⟩,
   ⟨199, 257, ⟨0, 2, false, true, false, 257, 257⟩⟩,
   ⟨258, 496, ⟨2, 7, false, true, false, 258, 258⟩⟩,
   ⟨497, 544, ⟨2, 7, false, false, false, 497, 497⟩⟩],
  [⟨182, 198, ⟨0, 2, true, true, false, 198, 198⟩⟩,
   ⟨199, 302, ⟨0, 2, false, true, false, 302, 302⟩⟩,
   ⟨303, 496, ⟨2, 7, false, true, false, 496, 496⟩⟩,
   ⟨497, 634, ⟨2, 7, false, false, false, 634, 634⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_258_lower : ConfigurationBounds 258 6238 139 := by
  apply configuration_of_cells 258 6238 139 data_258_lower
  decide +kernel

private def data_259_lower : Array (List Chunk) := #[
  [⟨1, 198, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨199, 212, ⟨0, 3, false, true, false, 199, 199⟩⟩,
   ⟨213, 456, ⟨3, 7, false, true, false, 213, 213⟩⟩],
  [⟨91, 198, ⟨0, 3, true, true, false, 198, 198⟩⟩,
   ⟨199, 258, ⟨0, 3, false, true, false, 258, 258⟩⟩,
   ⟨259, 502, ⟨3, 7, false, true, false, 259, 259⟩⟩],
  [⟨136, 198, ⟨0, 2, true, true, false, 198, 198⟩⟩,
   ⟨199, 258, ⟨0, 2, false, true, false, 258, 258⟩⟩,
   ⟨259, 510, ⟨2, 7, false, true, false, 259, 259⟩⟩,
   ⟨511, 547, ⟨2, 7, false, false, false, 511, 511⟩⟩],
  [⟨182, 198, ⟨0, 2, true, true, false, 198, 198⟩⟩,
   ⟨199, 303, ⟨0, 2, false, true, false, 303, 303⟩⟩,
   ⟨304, 510, ⟨2, 7, false, true, false, 510, 510⟩⟩,
   ⟨511, 637, ⟨2, 7, false, false, false, 637, 637⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_259_lower : ConfigurationBounds 259 6286 139 := by
  apply configuration_of_cells 259 6286 139 data_259_lower
  decide +kernel

private def data_260_lower : Array (List Chunk) := #[
  [⟨1, 199, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨200, 213, ⟨0, 3, false, true, false, 200, 200⟩⟩,
   ⟨214, 457, ⟨3, 7, false, true, false, 214, 214⟩⟩],
  [⟨92, 199, ⟨0, 3, true, true, false, 199, 199⟩⟩,
   ⟨200, 259, ⟨0, 3, false, true, false, 259, 259⟩⟩,
   ⟨260, 489, ⟨3, 7, false, true, false, 260, 260⟩⟩,
   ⟨490, 503, ⟨3, 7, false, false, false, 490, 490⟩⟩],
  [⟨137, 199, ⟨0, 2, true, true, false, 199, 199⟩⟩,
   ⟨200, 259, ⟨0, 2, false, true, false, 259, 259⟩⟩,
   ⟨260, 489, ⟨2, 7, false, true, false, 260, 260⟩⟩,
   ⟨490, 548, ⟨2, 7, false, false, false, 490, 490⟩⟩],
  [⟨183, 199, ⟨0, 2, true, true, false, 199, 199⟩⟩,
   ⟨200, 304, ⟨0, 2, false, true, false, 304, 304⟩⟩,
   ⟨305, 489, ⟨2, 7, false, true, false, 489, 489⟩⟩,
   ⟨490, 639, ⟨2, 7, false, false, false, 639, 639⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_260_lower : ConfigurationBounds 260 6334 140 := by
  apply configuration_of_cells 260 6334 140 data_260_lower
  decide +kernel

private def data_261_lower : Array (List Chunk) := #[
  [⟨1, 200, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨201, 214, ⟨0, 3, false, true, false, 201, 201⟩⟩,
   ⟨215, 432, ⟨3, 7, false, true, false, 215, 215⟩⟩,
   ⟨433, 458, ⟨3, 7, false, false, false, 433, 433⟩⟩],
  [⟨92, 200, ⟨0, 3, true, true, false, 200, 200⟩⟩,
   ⟨201, 260, ⟨0, 3, false, true, false, 260, 260⟩⟩,
   ⟨261, 432, ⟨3, 7, false, true, false, 261, 261⟩⟩,
   ⟨433, 504, ⟨3, 7, false, false, false, 433, 433⟩⟩],
  [⟨138, 200, ⟨0, 2, true, true, false, 200, 200⟩⟩,
   ⟨201, 260, ⟨0, 2, false, true, false, 260, 260⟩⟩,
   ⟨261, 432, ⟨2, 7, false, true, false, 261, 261⟩⟩,
   ⟨433, 550, ⟨2, 7, false, false, false, 433, 433⟩⟩],
  [⟨184, 200, ⟨0, 2, true, true, false, 200, 200⟩⟩,
   ⟨201, 306, ⟨0, 2, false, true, false, 306, 306⟩⟩,
   ⟨307, 432, ⟨2, 7, false, true, false, 432, 432⟩⟩,
   ⟨433, 641, ⟨2, 7, false, false, false, 641, 641⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_261_lower : ConfigurationBounds 261 6382 141 := by
  apply configuration_of_cells 261 6382 141 data_261_lower
  decide +kernel

private def data_262_lower : Array (List Chunk) := #[
  [⟨1, 201, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨202, 214, ⟨0, 3, false, true, false, 202, 202⟩⟩,
   ⟨215, 338, ⟨3, 7, false, true, false, 215, 215⟩⟩,
   ⟨339, 458, ⟨3, 7, false, false, false, 339, 339⟩⟩],
  [⟨93, 201, ⟨0, 3, true, true, false, 201, 201⟩⟩,
   ⟨202, 261, ⟨0, 3, false, true, false, 261, 261⟩⟩,
   ⟨262, 338, ⟨3, 7, false, true, false, 262, 262⟩⟩,
   ⟨339, 505, ⟨3, 7, false, false, false, 339, 339⟩⟩],
  [⟨139, 201, ⟨0, 2, true, true, false, 201, 201⟩⟩,
   ⟨202, 261, ⟨0, 2, false, true, false, 261, 261⟩⟩,
   ⟨262, 338, ⟨2, 7, false, true, false, 262, 262⟩⟩,
   ⟨339, 551, ⟨2, 7, false, false, false, 339, 339⟩⟩],
  [⟨186, 201, ⟨0, 2, true, true, false, 201, 201⟩⟩,
   ⟨202, 307, ⟨0, 2, false, true, false, 307, 307⟩⟩,
   ⟨308, 338, ⟨2, 7, false, true, false, 338, 338⟩⟩,
   ⟨339, 643, ⟨2, 7, false, false, false, 643, 643⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_262_lower : ConfigurationBounds 262 6430 142 := by
  apply configuration_of_cells 262 6430 142 data_262_lower
  decide +kernel

private def data_263_lower : Array (List Chunk) := #[
  [⟨1, 202, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨203, 215, ⟨0, 3, false, true, false, 203, 203⟩⟩,
   ⟨216, 404, ⟨3, 7, false, true, false, 216, 216⟩⟩,
   ⟨405, 461, ⟨3, 7, false, false, false, 405, 405⟩⟩],
  [⟨93, 202, ⟨0, 3, true, true, false, 202, 202⟩⟩,
   ⟨203, 262, ⟨0, 3, false, true, false, 262, 262⟩⟩,
   ⟨263, 404, ⟨3, 7, false, true, false, 263, 263⟩⟩,
   ⟨405, 508, ⟨3, 7, false, false, false, 405, 405⟩⟩],
  [⟨139, 202, ⟨0, 2, true, true, false, 202, 202⟩⟩,
   ⟨203, 262, ⟨0, 2, false, true, false, 262, 262⟩⟩,
   ⟨263, 404, ⟨2, 7, false, true, false, 263, 263⟩⟩,
   ⟨405, 554, ⟨2, 7, false, false, false, 405, 405⟩⟩],
  [⟨186, 202, ⟨0, 2, true, true, false, 202, 202⟩⟩,
   ⟨203, 308, ⟨0, 2, false, true, false, 308, 308⟩⟩,
   ⟨309, 404, ⟨2, 7, false, true, false, 404, 404⟩⟩,
   ⟨405, 646, ⟨2, 7, false, false, false, 646, 646⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_263_lower : ConfigurationBounds 263 6479 142 := by
  apply configuration_of_cells 263 6479 142 data_263_lower
  decide +kernel

private def data_264_lower : Array (List Chunk) := #[
  [⟨1, 203, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨204, 216, ⟨0, 3, false, true, false, 204, 204⟩⟩,
   ⟨217, 436, ⟨3, 7, false, true, false, 217, 217⟩⟩,
   ⟨437, 462, ⟨3, 7, false, false, false, 437, 437⟩⟩],
  [⟨94, 203, ⟨0, 3, true, true, false, 203, 203⟩⟩,
   ⟨204, 263, ⟨0, 3, false, true, false, 263, 263⟩⟩,
   ⟨264, 436, ⟨3, 7, false, true, false, 264, 264⟩⟩,
   ⟨437, 509, ⟨3, 7, false, false, false, 437, 437⟩⟩],
  [⟨140, 203, ⟨0, 2, true, true, false, 203, 203⟩⟩,
   ⟨204, 263, ⟨0, 2, false, true, false, 263, 263⟩⟩,
   ⟨264, 436, ⟨2, 7, false, true, false, 264, 264⟩⟩,
   ⟨437, 555, ⟨2, 7, false, false, false, 437, 437⟩⟩],
  [⟨187, 203, ⟨0, 2, true, true, false, 203, 203⟩⟩,
   ⟨204, 309, ⟨0, 2, false, true, false, 309, 309⟩⟩,
   ⟨310, 436, ⟨2, 7, false, true, false, 436, 436⟩⟩,
   ⟨437, 648, ⟨2, 7, false, false, false, 648, 648⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_264_lower : ConfigurationBounds 264 6528 143 := by
  apply configuration_of_cells 264 6528 143 data_264_lower
  decide +kernel

private def data_265_lower : Array (List Chunk) := #[
  [⟨1, 203, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨204, 217, ⟨0, 3, false, true, false, 204, 204⟩⟩,
   ⟨218, 429, ⟨3, 7, false, true, false, 218, 218⟩⟩,
   ⟨430, 465, ⟨3, 7, false, false, false, 430, 430⟩⟩],
  [⟨94, 203, ⟨0, 3, true, true, false, 203, 203⟩⟩,
   ⟨204, 264, ⟨0, 3, false, true, false, 264, 264⟩⟩,
   ⟨265, 429, ⟨3, 7, false, true, false, 265, 265⟩⟩,
   ⟨430, 512, ⟨3, 7, false, false, false, 430, 430⟩⟩],
  [⟨140, 203, ⟨0, 2, true, true, false, 203, 203⟩⟩,
   ⟨204, 264, ⟨0, 2, false, true, false, 264, 264⟩⟩,
   ⟨265, 429, ⟨2, 7, false, true, false, 265, 265⟩⟩,
   ⟨430, 558, ⟨2, 7, false, false, false, 430, 430⟩⟩],
  [⟨187, 203, ⟨0, 2, true, true, false, 203, 203⟩⟩,
   ⟨204, 310, ⟨0, 2, false, true, false, 310, 310⟩⟩,
   ⟨311, 429, ⟨2, 7, false, true, false, 429, 429⟩⟩,
   ⟨430, 651, ⟨2, 7, false, false, false, 651, 651⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_265_lower : ConfigurationBounds 265 6577 143 := by
  apply configuration_of_cells 265 6577 143 data_265_lower
  decide +kernel

private def data_266_lower : Array (List Chunk) := #[
  [⟨1, 204, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨205, 218, ⟨0, 3, false, true, false, 205, 205⟩⟩,
   ⟨219, 387, ⟨3, 7, false, true, false, 219, 219⟩⟩,
   ⟨388, 466, ⟨3, 7, false, false, false, 388, 388⟩⟩],
  [⟨94, 204, ⟨0, 3, true, true, false, 204, 204⟩⟩,
   ⟨205, 265, ⟨0, 3, false, true, false, 265, 265⟩⟩,
   ⟨266, 387, ⟨3, 7, false, true, false, 266, 266⟩⟩,
   ⟨388, 513, ⟨3, 7, false, false, false, 388, 388⟩⟩],
  [⟨141, 204, ⟨0, 2, true, true, false, 204, 204⟩⟩,
   ⟨205, 265, ⟨0, 2, false, true, false, 265, 265⟩⟩,
   ⟨266, 387, ⟨2, 7, false, true, false, 266, 266⟩⟩,
   ⟨388, 560, ⟨2, 7, false, false, false, 388, 388⟩⟩],
  [⟨188, 204, ⟨0, 2, true, true, false, 204, 204⟩⟩,
   ⟨205, 312, ⟨0, 2, false, true, false, 312, 312⟩⟩,
   ⟨313, 387, ⟨2, 7, false, true, false, 387, 387⟩⟩,
   ⟨388, 653, ⟨2, 7, false, false, false, 653, 653⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_266_lower : ConfigurationBounds 266 6626 144 := by
  apply configuration_of_cells 266 6626 144 data_266_lower
  decide +kernel

private def data_267_lower : Array (List Chunk) := #[
  [⟨1, 205, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨206, 219, ⟨0, 3, false, true, false, 206, 206⟩⟩,
   ⟨220, 469, ⟨3, 7, false, true, false, 220, 220⟩⟩],
  [⟨94, 205, ⟨0, 3, true, true, false, 205, 205⟩⟩,
   ⟨206, 266, ⟨0, 3, false, true, false, 266, 266⟩⟩,
   ⟨267, 508, ⟨3, 7, false, true, false, 267, 267⟩⟩,
   ⟨509, 516, ⟨3, 7, false, false, false, 509, 509⟩⟩],
  [⟨141, 205, ⟨0, 2, true, true, false, 205, 205⟩⟩,
   ⟨206, 266, ⟨0, 2, false, true, false, 266, 266⟩⟩,
   ⟨267, 508, ⟨2, 7, false, true, false, 267, 267⟩⟩,
   ⟨509, 563, ⟨2, 7, false, false, false, 509, 509⟩⟩],
  [⟨188, 205, ⟨0, 2, true, true, false, 205, 205⟩⟩,
   ⟨206, 313, ⟨0, 2, false, true, false, 313, 313⟩⟩,
   ⟨314, 508, ⟨2, 7, false, true, false, 508, 508⟩⟩,
   ⟨509, 656, ⟨2, 7, false, false, false, 656, 656⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_267_lower : ConfigurationBounds 267 6676 144 := by
  apply configuration_of_cells 267 6676 144 data_267_lower
  decide +kernel

private def data_268_lower : Array (List Chunk) := #[
  [⟨1, 206, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨207, 219, ⟨0, 3, false, true, false, 207, 207⟩⟩,
   ⟨220, 392, ⟨3, 7, false, true, false, 220, 220⟩⟩,
   ⟨393, 469, ⟨3, 7, false, false, false, 393, 393⟩⟩],
  [⟨95, 206, ⟨0, 3, true, true, false, 206, 206⟩⟩,
   ⟨207, 267, ⟨0, 3, false, true, false, 267, 267⟩⟩,
   ⟨268, 392, ⟨3, 7, false, true, false, 268, 268⟩⟩,
   ⟨393, 517, ⟨3, 7, false, false, false, 393, 393⟩⟩],
  [⟨142, 206, ⟨0, 2, true, true, false, 206, 206⟩⟩,
   ⟨207, 267, ⟨0, 2, false, true, false, 267, 267⟩⟩,
   ⟨268, 392, ⟨2, 7, false, true, false, 268, 268⟩⟩,
   ⟨393, 564, ⟨2, 7, false, false, false, 393, 393⟩⟩],
  [⟨190, 206, ⟨0, 2, true, true, false, 206, 206⟩⟩,
   ⟨207, 314, ⟨0, 2, false, true, false, 314, 314⟩⟩,
   ⟨315, 392, ⟨2, 7, false, true, false, 392, 392⟩⟩,
   ⟨393, 658, ⟨2, 7, false, false, false, 658, 658⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_268_lower : ConfigurationBounds 268 6725 145 := by
  apply configuration_of_cells 268 6725 145 data_268_lower
  decide +kernel

private def data_269_lower : Array (List Chunk) := #[
  [⟨1, 206, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨207, 220, ⟨0, 3, false, true, false, 207, 207⟩⟩,
   ⟨221, 439, ⟨3, 7, false, true, false, 221, 221⟩⟩,
   ⟨440, 472, ⟨3, 7, false, false, false, 440, 440⟩⟩],
  [⟨95, 206, ⟨0, 3, true, true, false, 206, 206⟩⟩,
   ⟨207, 268, ⟨0, 3, false, true, false, 268, 268⟩⟩,
   ⟨269, 439, ⟨3, 7, false, true, false, 269, 269⟩⟩,
   ⟨440, 520, ⟨3, 7, false, false, false, 440, 440⟩⟩],
  [⟨142, 206, ⟨0, 2, true, true, false, 206, 206⟩⟩,
   ⟨207, 268, ⟨0, 2, false, true, false, 268, 268⟩⟩,
   ⟨269, 439, ⟨2, 7, false, true, false, 269, 269⟩⟩,
   ⟨440, 567, ⟨2, 7, false, false, false, 440, 440⟩⟩],
  [⟨190, 206, ⟨0, 2, true, true, false, 206, 206⟩⟩,
   ⟨207, 315, ⟨0, 2, false, true, false, 315, 315⟩⟩,
   ⟨316, 439, ⟨2, 7, false, true, false, 439, 439⟩⟩,
   ⟨440, 661, ⟨2, 7, false, false, false, 661, 661⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_269_lower : ConfigurationBounds 269 6775 145 := by
  apply configuration_of_cells 269 6775 145 data_269_lower
  decide +kernel

private def data_270_lower : Array (List Chunk) := #[
  [⟨1, 207, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨208, 221, ⟨0, 3, false, true, false, 208, 208⟩⟩,
   ⟨222, 451, ⟨3, 7, false, true, false, 222, 222⟩⟩,
   ⟨452, 473, ⟨3, 7, false, false, false, 452, 452⟩⟩],
  [⟨96, 207, ⟨0, 3, true, true, false, 207, 207⟩⟩,
   ⟨208, 269, ⟨0, 3, false, true, false, 269, 269⟩⟩,
   ⟨270, 451, ⟨3, 7, false, true, false, 270, 270⟩⟩,
   ⟨452, 521, ⟨3, 7, false, false, false, 452, 452⟩⟩],
  [⟨143, 207, ⟨0, 2, true, true, false, 207, 207⟩⟩,
   ⟨208, 269, ⟨0, 2, false, true, false, 269, 269⟩⟩,
   ⟨270, 451, ⟨2, 7, false, true, false, 270, 270⟩⟩,
   ⟨452, 568, ⟨2, 7, false, false, false, 452, 452⟩⟩],
  [⟨191, 207, ⟨0, 2, true, true, false, 207, 207⟩⟩,
   ⟨208, 316, ⟨0, 2, false, true, false, 316, 316⟩⟩,
   ⟨317, 451, ⟨2, 7, false, true, false, 451, 451⟩⟩,
   ⟨452, 663, ⟨2, 7, false, false, false, 663, 663⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_270_lower : ConfigurationBounds 270 6825 146 := by
  apply configuration_of_cells 270 6825 146 data_270_lower
  decide +kernel

private def data_271_lower : Array (List Chunk) := #[
  [⟨1, 208, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨209, 222, ⟨0, 3, false, true, false, 209, 209⟩⟩,
   ⟨223, 425, ⟨3, 7, false, true, false, 223, 223⟩⟩,
   ⟨426, 474, ⟨3, 7, false, false, false, 426, 426⟩⟩],
  [⟨96, 208, ⟨0, 3, true, true, false, 208, 208⟩⟩,
   ⟨209, 270, ⟨0, 3, false, true, false, 270, 270⟩⟩,
   ⟨271, 425, ⟨3, 7, false, true, false, 271, 271⟩⟩,
   ⟨426, 522, ⟨3, 7, false, false, false, 426, 426⟩⟩],
  [⟨144, 208, ⟨0, 2, true, true, false, 208, 208⟩⟩,
   ⟨209, 270, ⟨0, 2, false, true, false, 270, 270⟩⟩,
   ⟨271, 425, ⟨2, 7, false, true, false, 271, 271⟩⟩,
   ⟨426, 570, ⟨2, 7, false, false, false, 426, 426⟩⟩],
  [⟨192, 208, ⟨0, 2, true, true, false, 208, 208⟩⟩,
   ⟨209, 318, ⟨0, 2, false, true, false, 318, 318⟩⟩,
   ⟨319, 425, ⟨2, 7, false, true, false, 425, 425⟩⟩,
   ⟨426, 665, ⟨2, 7, false, false, false, 665, 665⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_271_lower : ConfigurationBounds 271 6875 147 := by
  apply configuration_of_cells 271 6875 147 data_271_lower
  decide +kernel

private def data_272_lower : Array (List Chunk) := #[
  [⟨1, 209, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨210, 223, ⟨0, 3, false, true, false, 210, 210⟩⟩,
   ⟨224, 360, ⟨3, 7, false, true, false, 224, 224⟩⟩,
   ⟨361, 477, ⟨3, 7, false, false, false, 361, 361⟩⟩],
  [⟨96, 209, ⟨0, 3, true, true, false, 209, 209⟩⟩,
   ⟨210, 271, ⟨0, 3, false, true, false, 271, 271⟩⟩,
   ⟨272, 360, ⟨3, 7, false, true, false, 272, 272⟩⟩,
   ⟨361, 525, ⟨3, 7, false, false, false, 361, 361⟩⟩],
  [⟨144, 209, ⟨0, 2, true, true, false, 209, 209⟩⟩,
   ⟨210, 271, ⟨0, 2, false, true, false, 271, 271⟩⟩,
   ⟨272, 360, ⟨2, 7, false, true, false, 272, 272⟩⟩,
   ⟨361, 573, ⟨2, 7, false, false, false, 361, 361⟩⟩],
  [⟨192, 209, ⟨0, 2, true, true, false, 209, 209⟩⟩,
   ⟨210, 319, ⟨0, 2, false, true, false, 319, 319⟩⟩,
   ⟨320, 360, ⟨2, 7, false, true, false, 360, 360⟩⟩,
   ⟨361, 668, ⟨2, 7, false, false, false, 668, 668⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_272_lower : ConfigurationBounds 272 6925 147 := by
  apply configuration_of_cells 272 6925 147 data_272_lower
  decide +kernel

private def data_273_lower : Array (List Chunk) := #[
  [⟨1, 209, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨210, 224, ⟨0, 3, false, true, false, 210, 210⟩⟩,
   ⟨225, 463, ⟨3, 7, false, true, false, 225, 225⟩⟩,
   ⟨464, 480, ⟨3, 7, false, false, false, 464, 464⟩⟩],
  [⟨96, 209, ⟨0, 3, true, true, false, 209, 209⟩⟩,
   ⟨210, 272, ⟨0, 3, false, true, false, 272, 272⟩⟩,
   ⟨273, 463, ⟨3, 7, false, true, false, 273, 273⟩⟩,
   ⟨464, 528, ⟨3, 7, false, false, false, 464, 464⟩⟩],
  [⟨144, 209, ⟨0, 2, true, true, false, 209, 209⟩⟩,
   ⟨210, 272, ⟨0, 2, false, true, false, 272, 272⟩⟩,
   ⟨273, 463, ⟨2, 7, false, true, false, 273, 273⟩⟩,
   ⟨464, 576, ⟨2, 7, false, false, false, 464, 464⟩⟩],
  [⟨192, 209, ⟨0, 2, true, true, false, 209, 209⟩⟩,
   ⟨210, 320, ⟨0, 2, false, true, false, 320, 320⟩⟩,
   ⟨321, 463, ⟨2, 7, false, true, false, 463, 463⟩⟩,
   ⟨464, 671, ⟨2, 7, false, false, false, 671, 671⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_273_lower : ConfigurationBounds 273 6976 147 := by
  apply configuration_of_cells 273 6976 147 data_273_lower
  decide +kernel

private def data_274_lower : Array (List Chunk) := #[
  [⟨1, 210, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨211, 224, ⟨0, 3, false, true, false, 211, 211⟩⟩,
   ⟨225, 480, ⟨3, 7, false, true, false, 225, 225⟩⟩],
  [⟨97, 210, ⟨0, 3, true, true, false, 210, 210⟩⟩,
   ⟨211, 273, ⟨0, 3, false, true, false, 273, 273⟩⟩,
   ⟨274, 529, ⟨3, 7, false, true, false, 274, 274⟩⟩],
  [⟨145, 210, ⟨0, 2, true, true, false, 210, 210⟩⟩,
   ⟨211, 273, ⟨0, 2, false, true, false, 273, 273⟩⟩,
   ⟨274, 529, ⟨2, 7, false, true, false, 274, 274⟩⟩,
   ⟨530, 577, ⟨2, 7, false, false, false, 530, 530⟩⟩],
  [⟨194, 210, ⟨0, 2, true, true, false, 210, 210⟩⟩,
   ⟨211, 321, ⟨0, 2, false, true, false, 321, 321⟩⟩,
   ⟨322, 529, ⟨2, 7, false, true, false, 529, 529⟩⟩,
   ⟨530, 673, ⟨2, 7, false, false, false, 673, 673⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_274_lower : ConfigurationBounds 274 7027 148 := by
  apply configuration_of_cells 274 7027 148 data_274_lower
  decide +kernel

private def data_275_lower : Array (List Chunk) := #[
  [⟨1, 211, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨212, 225, ⟨0, 3, false, true, false, 212, 212⟩⟩,
   ⟨226, 351, ⟨3, 7, false, true, false, 226, 226⟩⟩,
   ⟨352, 481, ⟨3, 7, false, false, false, 352, 352⟩⟩],
  [⟨98, 211, ⟨0, 3, true, true, false, 211, 211⟩⟩,
   ⟨212, 274, ⟨0, 3, false, true, false, 274, 274⟩⟩,
   ⟨275, 351, ⟨3, 7, false, true, false, 275, 275⟩⟩,
   ⟨352, 530, ⟨3, 7, false, false, false, 352, 352⟩⟩],
  [⟨146, 211, ⟨0, 2, true, true, false, 211, 211⟩⟩,
   ⟨212, 274, ⟨0, 2, false, true, false, 274, 274⟩⟩,
   ⟨275, 351, ⟨2, 7, false, true, false, 275, 275⟩⟩,
   ⟨352, 578, ⟨2, 7, false, false, false, 352, 352⟩⟩],
  [⟨195, 211, ⟨0, 2, true, true, false, 211, 211⟩⟩,
   ⟨212, 322, ⟨0, 2, false, true, false, 322, 322⟩⟩,
   ⟨323, 351, ⟨2, 7, false, true, false, 351, 351⟩⟩,
   ⟨352, 675, ⟨2, 7, false, false, false, 675, 675⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_275_lower : ConfigurationBounds 275 7077 149 := by
  apply configuration_of_cells 275 7077 149 data_275_lower
  decide +kernel

private def data_276_lower : Array (List Chunk) := #[
  [⟨1, 212, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨213, 226, ⟨0, 3, false, true, false, 213, 213⟩⟩,
   ⟨227, 342, ⟨3, 7, false, true, false, 227, 227⟩⟩,
   ⟨343, 482, ⟨3, 7, false, false, false, 343, 343⟩⟩],
  [⟨98, 212, ⟨0, 3, true, true, false, 212, 212⟩⟩,
   ⟨213, 275, ⟨0, 3, false, true, false, 275, 275⟩⟩,
   ⟨276, 342, ⟨3, 7, false, true, false, 276, 276⟩⟩,
   ⟨343, 531, ⟨3, 7, false, false, false, 343, 343⟩⟩],
  [⟨147, 212, ⟨0, 2, true, true, false, 212, 212⟩⟩,
   ⟨213, 275, ⟨0, 2, false, true, false, 275, 275⟩⟩,
   ⟨276, 342, ⟨2, 7, false, true, false, 276, 276⟩⟩,
   ⟨343, 580, ⟨2, 7, false, false, false, 343, 343⟩⟩],
  [⟨196, 212, ⟨0, 2, true, true, false, 212, 212⟩⟩,
   ⟨213, 324, ⟨0, 2, false, true, false, 324, 324⟩⟩,
   ⟨325, 342, ⟨2, 7, false, true, false, 342, 342⟩⟩,
   ⟨343, 677, ⟨2, 7, false, false, false, 677, 677⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_276_lower : ConfigurationBounds 276 7128 150 := by
  apply configuration_of_cells 276 7128 150 data_276_lower
  decide +kernel

private def data_277_lower : Array (List Chunk) := #[
  [⟨1, 213, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨214, 227, ⟨0, 3, false, true, false, 214, 214⟩⟩,
   ⟨228, 485, ⟨3, 7, false, true, false, 228, 228⟩⟩],
  [⟨98, 213, ⟨0, 3, true, true, false, 213, 213⟩⟩,
   ⟨214, 276, ⟨0, 3, false, true, false, 276, 276⟩⟩,
   ⟨277, 501, ⟨3, 7, false, true, false, 277, 277⟩⟩,
   ⟨502, 534, ⟨3, 7, false, false, false, 502, 502⟩⟩],
  [⟨147, 213, ⟨0, 2, true, true, false, 213, 213⟩⟩,
   ⟨214, 276, ⟨0, 2, false, true, false, 276, 276⟩⟩,
   ⟨277, 501, ⟨2, 7, false, true, false, 277, 277⟩⟩,
   ⟨502, 583, ⟨2, 7, false, false, false, 502, 502⟩⟩],
  [⟨196, 213, ⟨0, 2, true, true, false, 213, 213⟩⟩,
   ⟨214, 325, ⟨0, 2, false, true, false, 325, 325⟩⟩,
   ⟨326, 501, ⟨2, 7, false, true, false, 501, 501⟩⟩,
   ⟨502, 680, ⟨2, 7, false, false, false, 680, 680⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_277_lower : ConfigurationBounds 277 7180 150 := by
  apply configuration_of_cells 277 7180 150 data_277_lower
  decide +kernel

private def data_278_lower : Array (List Chunk) := #[
  [⟨1, 214, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨215, 227, ⟨0, 3, false, true, false, 215, 215⟩⟩,
   ⟨228, 415, ⟨3, 7, false, true, false, 228, 228⟩⟩,
   ⟨416, 485, ⟨3, 7, false, false, false, 416, 416⟩⟩],
  [⟨99, 214, ⟨0, 3, true, true, false, 214, 214⟩⟩,
   ⟨215, 277, ⟨0, 3, false, true, false, 277, 277⟩⟩,
   ⟨278, 415, ⟨3, 7, false, true, false, 278, 278⟩⟩,
   ⟨416, 535, ⟨3, 7, false, false, false, 416, 416⟩⟩],
  [⟨148, 214, ⟨0, 2, true, true, false, 214, 214⟩⟩,
   ⟨215, 277, ⟨0, 2, false, true, false, 277, 277⟩⟩,
   ⟨278, 415, ⟨2, 7, false, true, false, 278, 278⟩⟩,
   ⟨416, 584, ⟨2, 7, false, false, false, 416, 416⟩⟩],
  [⟨198, 214, ⟨0, 2, true, true, false, 214, 214⟩⟩,
   ⟨215, 326, ⟨0, 2, false, true, false, 326, 326⟩⟩,
   ⟨327, 415, ⟨2, 7, false, true, false, 415, 415⟩⟩,
   ⟨416, 682, ⟨2, 7, false, false, false, 682, 682⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_278_lower : ConfigurationBounds 278 7231 151 := by
  apply configuration_of_cells 278 7231 151 data_278_lower
  decide +kernel

private def data_279_lower : Array (List Chunk) := #[
  [⟨1, 214, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨215, 228, ⟨0, 3, false, true, false, 215, 215⟩⟩,
   ⟨229, 488, ⟨3, 7, false, true, false, 229, 229⟩⟩],
  [⟨99, 214, ⟨0, 3, true, true, false, 214, 214⟩⟩,
   ⟨215, 278, ⟨0, 3, false, true, false, 278, 278⟩⟩,
   ⟨279, 499, ⟨3, 7, false, true, false, 279, 279⟩⟩,
   ⟨500, 538, ⟨3, 7, false, false, false, 500, 500⟩⟩],
  [⟨148, 214, ⟨0, 2, true, true, false, 214, 214⟩⟩,
   ⟨215, 278, ⟨0, 2, false, true, false, 278, 278⟩⟩,
   ⟨279, 499, ⟨2, 7, false, true, false, 279, 279⟩⟩,
   ⟨500, 587, ⟨2, 7, false, false, false, 500, 500⟩⟩],
  [⟨198, 214, ⟨0, 2, true, true, false, 214, 214⟩⟩,
   ⟨215, 327, ⟨0, 2, false, true, false, 327, 327⟩⟩,
   ⟨328, 499, ⟨2, 7, false, true, false, 499, 499⟩⟩,
   ⟨500, 685, ⟨2, 7, false, false, false, 685, 685⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_279_lower : ConfigurationBounds 279 7283 151 := by
  apply configuration_of_cells 279 7283 151 data_279_lower
  decide +kernel

private def data_280_lower : Array (List Chunk) := #[
  [⟨1, 215, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨216, 229, ⟨0, 3, false, true, false, 216, 216⟩⟩,
   ⟨230, 491, ⟨3, 7, false, true, false, 230, 230⟩⟩],
  [⟨99, 215, ⟨0, 3, true, true, false, 215, 215⟩⟩,
   ⟨216, 279, ⟨0, 3, false, true, false, 279, 279⟩⟩,
   ⟨280, 541, ⟨3, 7, false, true, false, 280, 280⟩⟩],
  [⟨148, 215, ⟨0, 2, true, true, false, 215, 215⟩⟩,
   ⟨216, 279, ⟨0, 2, false, true, false, 279, 279⟩⟩,
   ⟨280, 544, ⟨2, 7, false, true, false, 280, 280⟩⟩,
   ⟨545, 590, ⟨2, 7, false, false, false, 545, 545⟩⟩],
  [⟨198, 215, ⟨0, 2, true, true, false, 215, 215⟩⟩,
   ⟨216, 328, ⟨0, 2, false, true, false, 328, 328⟩⟩,
   ⟨329, 544, ⟨2, 7, false, true, false, 544, 544⟩⟩,
   ⟨545, 688, ⟨2, 7, false, false, false, 688, 688⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_280_lower : ConfigurationBounds 280 7335 151 := by
  apply configuration_of_cells 280 7335 151 data_280_lower
  decide +kernel

private def data_281_lower : Array (List Chunk) := #[
  [⟨1, 216, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨217, 230, ⟨0, 3, false, true, false, 217, 217⟩⟩,
   ⟨231, 492, ⟨3, 7, false, true, false, 231, 231⟩⟩],
  [⟨100, 216, ⟨0, 3, true, true, false, 216, 216⟩⟩,
   ⟨217, 280, ⟨0, 3, false, true, false, 280, 280⟩⟩,
   ⟨281, 542, ⟨3, 7, false, true, false, 281, 281⟩⟩],
  [⟨149, 216, ⟨0, 2, true, true, false, 216, 216⟩⟩,
   ⟨217, 280, ⟨0, 2, false, true, false, 280, 280⟩⟩,
   ⟨281, 553, ⟨2, 7, false, true, false, 281, 281⟩⟩,
   ⟨554, 591, ⟨2, 7, false, false, false, 554, 554⟩⟩],
  [⟨199, 216, ⟨0, 2, true, true, false, 216, 216⟩⟩,
   ⟨217, 329, ⟨0, 2, false, true, false, 329, 329⟩⟩,
   ⟨330, 553, ⟨2, 7, false, true, false, 553, 553⟩⟩,
   ⟨554, 690, ⟨2, 7, false, false, false, 690, 690⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_281_lower : ConfigurationBounds 281 7387 152 := by
  apply configuration_of_cells 281 7387 152 data_281_lower
  decide +kernel

private def data_282_lower : Array (List Chunk) := #[
  [⟨1, 216, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨217, 231, ⟨0, 3, false, true, false, 217, 217⟩⟩,
   ⟨232, 495, ⟨3, 7, false, true, false, 232, 232⟩⟩],
  [⟨100, 216, ⟨0, 3, true, true, false, 216, 216⟩⟩,
   ⟨217, 281, ⟨0, 3, false, true, false, 281, 281⟩⟩,
   ⟨282, 521, ⟨3, 7, false, true, false, 282, 282⟩⟩,
   ⟨522, 545, ⟨3, 7, false, false, false, 522, 522⟩⟩],
  [⟨149, 216, ⟨0, 2, true, true, false, 216, 216⟩⟩,
   ⟨217, 281, ⟨0, 2, false, true, false, 281, 281⟩⟩,
   ⟨282, 521, ⟨2, 7, false, true, false, 282, 282⟩⟩,
   ⟨522, 594, ⟨2, 7, false, false, false, 522, 522⟩⟩],
  [⟨199, 216, ⟨0, 2, true, true, false, 216, 216⟩⟩,
   ⟨217, 330, ⟨0, 2, false, true, false, 330, 330⟩⟩,
   ⟨331, 521, ⟨2, 7, false, true, false, 521, 521⟩⟩,
   ⟨522, 693, ⟨2, 7, false, false, false, 693, 693⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_282_lower : ConfigurationBounds 282 7439 152 := by
  apply configuration_of_cells 282 7439 152 data_282_lower
  decide +kernel

private def data_283_lower : Array (List Chunk) := #[
  [⟨1, 217, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨218, 232, ⟨0, 3, false, true, false, 218, 218⟩⟩,
   ⟨233, 451, ⟨3, 7, false, true, false, 233, 233⟩⟩,
   ⟨452, 496, ⟨3, 7, false, false, false, 452, 452⟩⟩],
  [⟨100, 217, ⟨0, 3, true, true, false, 217, 217⟩⟩,
   ⟨218, 282, ⟨0, 3, false, true, false, 282, 282⟩⟩,
   ⟨283, 451, ⟨3, 7, false, true, false, 283, 283⟩⟩,
   ⟨452, 546, ⟨3, 7, false, false, false, 452, 452⟩⟩],
  [⟨150, 217, ⟨0, 2, true, true, false, 217, 217⟩⟩,
   ⟨218, 282, ⟨0, 2, false, true, false, 282, 282⟩⟩,
   ⟨283, 451, ⟨2, 7, false, true, false, 283, 283⟩⟩,
   ⟨452, 596, ⟨2, 7, false, false, false, 452, 452⟩⟩],
  [⟨200, 217, ⟨0, 2, true, true, false, 217, 217⟩⟩,
   ⟨218, 332, ⟨0, 2, false, true, false, 332, 332⟩⟩,
   ⟨333, 451, ⟨2, 7, false, true, false, 451, 451⟩⟩,
   ⟨452, 695, ⟨2, 7, false, false, false, 695, 695⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_283_lower : ConfigurationBounds 283 7491 153 := by
  apply configuration_of_cells 283 7491 153 data_283_lower
  decide +kernel

private def data_284_lower : Array (List Chunk) := #[
  [⟨1, 218, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨219, 233, ⟨0, 3, false, true, false, 219, 219⟩⟩,
   ⟨234, 499, ⟨3, 7, false, true, false, 234, 234⟩⟩],
  [⟨100, 218, ⟨0, 3, true, true, false, 218, 218⟩⟩,
   ⟨219, 283, ⟨0, 3, false, true, false, 283, 283⟩⟩,
   ⟨284, 549, ⟨3, 7, false, true, false, 284, 284⟩⟩],
  [⟨150, 218, ⟨0, 2, true, true, false, 218, 218⟩⟩,
   ⟨219, 283, ⟨0, 2, false, true, false, 283, 283⟩⟩,
   ⟨284, 554, ⟨2, 7, false, true, false, 284, 284⟩⟩,
   ⟨555, 599, ⟨2, 7, false, false, false, 555, 555⟩⟩],
  [⟨200, 218, ⟨0, 2, true, true, false, 218, 218⟩⟩,
   ⟨219, 333, ⟨0, 2, false, true, false, 333, 333⟩⟩,
   ⟨334, 554, ⟨2, 7, false, true, false, 554, 554⟩⟩,
   ⟨555, 698, ⟨2, 7, false, false, false, 698, 698⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_284_lower : ConfigurationBounds 284 7544 153 := by
  apply configuration_of_cells 284 7544 153 data_284_lower
  decide +kernel

private def data_285_lower : Array (List Chunk) := #[
  [⟨1, 219, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨220, 233, ⟨0, 3, false, true, false, 220, 220⟩⟩,
   ⟨234, 404, ⟨3, 7, false, true, false, 234, 234⟩⟩,
   ⟨405, 499, ⟨3, 7, false, false, false, 405, 405⟩⟩],
  [⟨101, 219, ⟨0, 3, true, true, false, 219, 219⟩⟩,
   ⟨220, 284, ⟨0, 3, false, true, false, 284, 284⟩⟩,
   ⟨285, 404, ⟨3, 7, false, true, false, 285, 285⟩⟩,
   ⟨405, 550, ⟨3, 7, false, false, false, 405, 405⟩⟩],
  [⟨151, 219, ⟨0, 2, true, true, false, 219, 219⟩⟩,
   ⟨220, 284, ⟨0, 2, false, true, false, 284, 284⟩⟩,
   ⟨285, 404, ⟨2, 7, false, true, false, 285, 285⟩⟩,
   ⟨405, 600, ⟨2, 7, false, false, false, 405, 405⟩⟩],
  [⟨202, 219, ⟨0, 2, true, true, false, 219, 219⟩⟩,
   ⟨220, 334, ⟨0, 2, false, true, false, 334, 334⟩⟩,
   ⟨335, 404, ⟨2, 7, false, true, false, 404, 404⟩⟩,
   ⟨405, 700, ⟨2, 7, false, false, false, 700, 700⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_285_lower : ConfigurationBounds 285 7596 154 := by
  apply configuration_of_cells 285 7596 154 data_285_lower
  decide +kernel

private def data_286_lower : Array (List Chunk) := #[
  [⟨1, 220, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨221, 234, ⟨0, 3, false, true, false, 221, 221⟩⟩,
   ⟨235, 430, ⟨3, 7, false, true, false, 235, 235⟩⟩,
   ⟨431, 500, ⟨3, 7, false, false, false, 431, 431⟩⟩],
  [⟨102, 220, ⟨0, 3, true, true, false, 220, 220⟩⟩,
   ⟨221, 285, ⟨0, 3, false, true, false, 285, 285⟩⟩,
   ⟨286, 430, ⟨3, 7, false, true, false, 286, 286⟩⟩,
   ⟨431, 551, ⟨3, 7, false, false, false, 431, 431⟩⟩],
  [⟨152, 220, ⟨0, 2, true, true, false, 220, 220⟩⟩,
   ⟨221, 285, ⟨0, 2, false, true, false, 285, 285⟩⟩,
   ⟨286, 430, ⟨2, 7, false, true, false, 286, 286⟩⟩,
   ⟨431, 601, ⟨2, 7, false, false, false, 431, 431⟩⟩],
  [⟨203, 220, ⟨0, 2, true, true, false, 220, 220⟩⟩,
   ⟨221, 335, ⟨0, 2, false, true, false, 335, 335⟩⟩,
   ⟨336, 430, ⟨2, 7, false, true, false, 430, 430⟩⟩,
   ⟨431, 702, ⟨2, 7, false, false, false, 702, 702⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_286_lower : ConfigurationBounds 286 7649 155 := by
  apply configuration_of_cells 286 7649 155 data_286_lower
  decide +kernel

private def data_287_lower : Array (List Chunk) := #[
  [⟨1, 221, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨222, 235, ⟨0, 3, false, true, false, 222, 222⟩⟩,
   ⟨236, 416, ⟨3, 7, false, true, false, 236, 236⟩⟩,
   ⟨417, 501, ⟨3, 7, false, false, false, 417, 417⟩⟩],
  [⟨102, 221, ⟨0, 3, true, true, false, 221, 221⟩⟩,
   ⟨222, 286, ⟨0, 3, false, true, false, 286, 286⟩⟩,
   ⟨287, 416, ⟨3, 7, false, true, false, 287, 287⟩⟩,
   ⟨417, 552, ⟨3, 7, false, false, false, 417, 417⟩⟩],
  [⟨153, 221, ⟨0, 2, true, true, false, 221, 221⟩⟩,
   ⟨222, 286, ⟨0, 2, false, true, false, 286, 286⟩⟩,
   ⟨287, 416, ⟨2, 7, false, true, false, 287, 287⟩⟩,
   ⟨417, 603, ⟨2, 7, false, false, false, 417, 417⟩⟩],
  [⟨204, 221, ⟨0, 2, true, true, false, 221, 221⟩⟩,
   ⟨222, 337, ⟨0, 2, false, true, false, 337, 337⟩⟩,
   ⟨338, 416, ⟨2, 7, false, true, false, 416, 416⟩⟩,
   ⟨417, 704, ⟨2, 7, false, false, false, 704, 704⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_287_lower : ConfigurationBounds 287 7702 156 := by
  apply configuration_of_cells 287 7702 156 data_287_lower
  decide +kernel

private def data_288_lower : Array (List Chunk) := #[
  [⟨1, 221, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨222, 236, ⟨0, 3, false, true, false, 222, 222⟩⟩,
   ⟨237, 361, ⟨3, 7, false, true, false, 237, 237⟩⟩,
   ⟨362, 504, ⟨3, 7, false, false, false, 362, 362⟩⟩],
  [⟨102, 221, ⟨0, 3, true, true, false, 221, 221⟩⟩,
   ⟨222, 287, ⟨0, 3, false, true, false, 287, 287⟩⟩,
   ⟨288, 361, ⟨3, 7, false, true, false, 288, 288⟩⟩,
   ⟨362, 555, ⟨3, 7, false, false, false, 362, 362⟩⟩],
  [⟨153, 221, ⟨0, 2, true, true, false, 221, 221⟩⟩,
   ⟨222, 287, ⟨0, 2, false, true, false, 287, 287⟩⟩,
   ⟨288, 361, ⟨2, 7, false, true, false, 288, 288⟩⟩,
   ⟨362, 606, ⟨2, 7, false, false, false, 362, 362⟩⟩],
  [⟨204, 221, ⟨0, 2, true, true, false, 221, 221⟩⟩,
   ⟨222, 338, ⟨0, 2, false, true, false, 338, 338⟩⟩,
   ⟨339, 361, ⟨2, 7, false, true, false, 361, 361⟩⟩,
   ⟨362, 707, ⟨2, 7, false, false, false, 707, 707⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_288_lower : ConfigurationBounds 288 7755 156 := by
  apply configuration_of_cells 288 7755 156 data_288_lower
  decide +kernel

private def data_289_lower : Array (List Chunk) := #[
  [⟨1, 222, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨223, 237, ⟨0, 3, false, true, false, 223, 223⟩⟩,
   ⟨238, 483, ⟨3, 7, false, true, false, 238, 238⟩⟩,
   ⟨484, 507, ⟨3, 7, false, false, false, 484, 484⟩⟩],
  [⟨102, 222, ⟨0, 3, true, true, false, 222, 222⟩⟩,
   ⟨223, 288, ⟨0, 3, false, true, false, 288, 288⟩⟩,
   ⟨289, 483, ⟨3, 7, false, true, false, 289, 289⟩⟩,
   ⟨484, 558, ⟨3, 7, false, false, false, 484, 484⟩⟩],
  [⟨153, 222, ⟨0, 2, true, true, false, 222, 222⟩⟩,
   ⟨223, 288, ⟨0, 2, false, true, false, 288, 288⟩⟩,
   ⟨289, 483, ⟨2, 7, false, true, false, 289, 289⟩⟩,
   ⟨484, 609, ⟨2, 7, false, false, false, 484, 484⟩⟩],
  [⟨204, 222, ⟨0, 2, true, true, false, 222, 222⟩⟩,
   ⟨223, 339, ⟨0, 2, false, true, false, 339, 339⟩⟩,
   ⟨340, 483, ⟨2, 7, false, true, false, 483, 483⟩⟩,
   ⟨484, 710, ⟨2, 7, false, false, false, 710, 710⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_289_lower : ConfigurationBounds 289 7809 156 := by
  apply configuration_of_cells 289 7809 156 data_289_lower
  decide +kernel

private def data_290_lower : Array (List Chunk) := #[
  [⟨1, 222, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨223, 238, ⟨0, 3, false, true, false, 223, 223⟩⟩,
   ⟨239, 510, ⟨3, 7, false, true, false, 239, 239⟩⟩],
  [⟨102, 222, ⟨0, 3, true, true, false, 222, 222⟩⟩,
   ⟨223, 289, ⟨0, 3, false, true, false, 289, 289⟩⟩,
   ⟨290, 561, ⟨3, 7, false, true, false, 290, 290⟩⟩],
  [⟨153, 222, ⟨0, 2, true, true, false, 222, 222⟩⟩,
   ⟨223, 289, ⟨0, 2, false, true, false, 289, 289⟩⟩,
   ⟨290, 567, ⟨2, 7, false, true, false, 290, 290⟩⟩,
   ⟨568, 612, ⟨2, 7, false, false, false, 568, 568⟩⟩],
  [⟨204, 222, ⟨0, 2, true, true, false, 222, 222⟩⟩,
   ⟨223, 340, ⟨0, 2, false, true, false, 340, 340⟩⟩,
   ⟨341, 567, ⟨2, 7, false, true, false, 567, 567⟩⟩,
   ⟨568, 713, ⟨2, 7, false, false, false, 713, 713⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_290_lower : ConfigurationBounds 290 7863 156 := by
  apply configuration_of_cells 290 7863 156 data_290_lower
  decide +kernel

private def data_291_lower : Array (List Chunk) := #[
  [⟨1, 224, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨225, 238, ⟨0, 3, false, true, false, 225, 225⟩⟩,
   ⟨239, 393, ⟨3, 7, false, true, false, 239, 239⟩⟩,
   ⟨394, 508, ⟨3, 7, false, false, false, 394, 394⟩⟩],
  [⟨104, 224, ⟨0, 3, true, true, false, 224, 224⟩⟩,
   ⟨225, 290, ⟨0, 3, false, true, false, 290, 290⟩⟩,
   ⟨291, 393, ⟨3, 7, false, true, false, 291, 291⟩⟩,
   ⟨394, 560, ⟨3, 7, false, false, false, 394, 394⟩⟩],
  [⟨155, 224, ⟨0, 2, true, true, false, 224, 224⟩⟩,
   ⟨225, 290, ⟨0, 2, false, true, false, 290, 290⟩⟩,
   ⟨291, 393, ⟨2, 7, false, true, false, 291, 291⟩⟩,
   ⟨394, 611, ⟨2, 7, false, false, false, 394, 394⟩⟩],
  [⟨207, 224, ⟨0, 2, true, true, false, 224, 224⟩⟩,
   ⟨225, 341, ⟨0, 2, false, true, false, 341, 341⟩⟩,
   ⟨342, 393, ⟨2, 7, false, true, false, 393, 393⟩⟩,
   ⟨394, 714, ⟨2, 7, false, false, false, 714, 714⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_291_lower : ConfigurationBounds 291 7916 158 := by
  apply configuration_of_cells 291 7916 158 data_291_lower
  decide +kernel

private def data_292_lower : Array (List Chunk) := #[
  [⟨1, 224, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨225, 239, ⟨0, 3, false, true, false, 225, 225⟩⟩,
   ⟨240, 396, ⟨3, 7, false, true, false, 240, 240⟩⟩,
   ⟨397, 511, ⟨3, 7, false, false, false, 397, 397⟩⟩],
  [⟨104, 224, ⟨0, 3, true, true, false, 224, 224⟩⟩,
   ⟨225, 291, ⟨0, 3, false, true, false, 291, 291⟩⟩,
   ⟨292, 396, ⟨3, 7, false, true, false, 292, 292⟩⟩,
   ⟨397, 563, ⟨3, 7, false, false, false, 397, 397⟩⟩],
  [⟨155, 224, ⟨0, 2, true, true, false, 224, 224⟩⟩,
   ⟨225, 291, ⟨0, 2, false, true, false, 291, 291⟩⟩,
   ⟨292, 396, ⟨2, 7, false, true, false, 292, 292⟩⟩,
   ⟨397, 614, ⟨2, 7, false, false, false, 397, 397⟩⟩],
  [⟨207, 224, ⟨0, 2, true, true, false, 224, 224⟩⟩,
   ⟨225, 342, ⟨0, 2, false, true, false, 342, 342⟩⟩,
   ⟨343, 396, ⟨2, 7, false, true, false, 396, 396⟩⟩,
   ⟨397, 717, ⟨2, 7, false, false, false, 717, 717⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_292_lower : ConfigurationBounds 292 7970 158 := by
  apply configuration_of_cells 292 7970 158 data_292_lower
  decide +kernel

private def data_293_lower : Array (List Chunk) := #[
  [⟨1, 225, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨226, 240, ⟨0, 3, false, true, false, 226, 226⟩⟩,
   ⟨241, 359, ⟨3, 7, false, true, false, 241, 241⟩⟩,
   ⟨360, 512, ⟨3, 7, false, false, false, 360, 360⟩⟩],
  [⟨104, 225, ⟨0, 3, true, true, false, 225, 225⟩⟩,
   ⟨226, 292, ⟨0, 3, false, true, false, 292, 292⟩⟩,
   ⟨293, 359, ⟨3, 7, false, true, false, 293, 293⟩⟩,
   ⟨360, 564, ⟨3, 7, false, false, false, 360, 360⟩⟩],
  [⟨156, 225, ⟨0, 2, true, true, false, 225, 225⟩⟩,
   ⟨226, 292, ⟨0, 2, false, true, false, 292, 292⟩⟩,
   ⟨293, 359, ⟨2, 7, false, true, false, 293, 293⟩⟩,
   ⟨360, 616, ⟨2, 7, false, false, false, 360, 360⟩⟩],
  [⟨208, 225, ⟨0, 2, true, true, false, 225, 225⟩⟩,
   ⟨226, 344, ⟨0, 2, false, true, false, 344, 344⟩⟩,
   ⟨345, 359, ⟨2, 7, false, true, false, 359, 359⟩⟩,
   ⟨360, 719, ⟨2, 7, false, false, false, 719, 719⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_293_lower : ConfigurationBounds 293 8024 159 := by
  apply configuration_of_cells 293 8024 159 data_293_lower
  decide +kernel

private def data_294_lower : Array (List Chunk) := #[
  [⟨1, 226, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨227, 241, ⟨0, 3, false, true, false, 227, 227⟩⟩,
   ⟨242, 502, ⟨3, 7, false, true, false, 242, 242⟩⟩,
   ⟨503, 515, ⟨3, 7, false, false, false, 503, 503⟩⟩],
  [⟨104, 226, ⟨0, 3, true, true, false, 226, 226⟩⟩,
   ⟨227, 293, ⟨0, 3, false, true, false, 293, 293⟩⟩,
   ⟨294, 502, ⟨3, 7, false, true, false, 294, 294⟩⟩,
   ⟨503, 567, ⟨3, 7, false, false, false, 503, 503⟩⟩],
  [⟨156, 226, ⟨0, 2, true, true, false, 226, 226⟩⟩,
   ⟨227, 293, ⟨0, 2, false, true, false, 293, 293⟩⟩,
   ⟨294, 502, ⟨2, 7, false, true, false, 294, 294⟩⟩,
   ⟨503, 619, ⟨2, 7, false, false, false, 503, 503⟩⟩],
  [⟨208, 226, ⟨0, 2, true, true, false, 226, 226⟩⟩,
   ⟨227, 345, ⟨0, 2, false, true, false, 345, 345⟩⟩,
   ⟨346, 502, ⟨2, 7, false, true, false, 502, 502⟩⟩,
   ⟨503, 722, ⟨2, 7, false, false, false, 722, 722⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_294_lower : ConfigurationBounds 294 8079 159 := by
  apply configuration_of_cells 294 8079 159 data_294_lower
  decide +kernel

private def data_295_lower : Array (List Chunk) := #[
  [⟨1, 227, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨228, 241, ⟨0, 3, false, true, false, 228, 228⟩⟩,
   ⟨242, 384, ⟨3, 7, false, true, false, 242, 242⟩⟩,
   ⟨385, 515, ⟨3, 7, false, false, false, 385, 385⟩⟩],
  [⟨105, 227, ⟨0, 3, true, true, false, 227, 227⟩⟩,
   ⟨228, 294, ⟨0, 3, false, true, false, 294, 294⟩⟩,
   ⟨295, 384, ⟨3, 7, false, true, false, 295, 295⟩⟩,
   ⟨385, 568, ⟨3, 7, false, false, false, 385, 385⟩⟩],
  [⟨157, 227, ⟨0, 2, true, true, false, 227, 227⟩⟩,
   ⟨228, 294, ⟨0, 2, false, true, false, 294, 294⟩⟩,
   ⟨295, 384, ⟨2, 7, false, true, false, 295, 295⟩⟩,
   ⟨385, 620, ⟨2, 7, false, false, false, 385, 385⟩⟩],
  [⟨210, 227, ⟨0, 2, true, true, false, 227, 227⟩⟩,
   ⟨228, 346, ⟨0, 2, false, true, false, 346, 346⟩⟩,
   ⟨347, 384, ⟨2, 7, false, true, false, 384, 384⟩⟩,
   ⟨385, 724, ⟨2, 7, false, false, false, 724, 724⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_295_lower : ConfigurationBounds 295 8133 160 := by
  apply configuration_of_cells 295 8133 160 data_295_lower
  decide +kernel

private def data_296_lower : Array (List Chunk) := #[
  [⟨1, 227, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨228, 242, ⟨0, 3, false, true, false, 228, 228⟩⟩,
   ⟨243, 445, ⟨3, 7, false, true, false, 243, 243⟩⟩,
   ⟨446, 518, ⟨3, 7, false, false, false, 446, 446⟩⟩],
  [⟨105, 227, ⟨0, 3, true, true, false, 227, 227⟩⟩,
   ⟨228, 295, ⟨0, 3, false, true, false, 295, 295⟩⟩,
   ⟨296, 445, ⟨3, 7, false, true, false, 296, 296⟩⟩,
   ⟨446, 571, ⟨3, 7, false, false, false, 446, 446⟩⟩],
  [⟨157, 227, ⟨0, 2, true, true, false, 227, 227⟩⟩,
   ⟨228, 295, ⟨0, 2, false, true, false, 295, 295⟩⟩,
   ⟨296, 445, ⟨2, 7, false, true, false, 296, 296⟩⟩,
   ⟨446, 623, ⟨2, 7, false, false, false, 446, 446⟩⟩],
  [⟨210, 227, ⟨0, 2, true, true, false, 227, 227⟩⟩,
   ⟨228, 347, ⟨0, 2, false, true, false, 347, 347⟩⟩,
   ⟨348, 445, ⟨2, 7, false, true, false, 445, 445⟩⟩,
   ⟨446, 727, ⟨2, 7, false, false, false, 727, 727⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_296_lower : ConfigurationBounds 296 8188 160 := by
  apply configuration_of_cells 296 8188 160 data_296_lower
  decide +kernel

private def data_297_lower : Array (List Chunk) := #[
  [⟨1, 228, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨229, 243, ⟨0, 3, false, true, false, 229, 229⟩⟩,
   ⟨244, 468, ⟨3, 7, false, true, false, 244, 244⟩⟩,
   ⟨469, 519, ⟨3, 7, false, false, false, 469, 469⟩⟩],
  [⟨106, 228, ⟨0, 3, true, true, false, 228, 228⟩⟩,
   ⟨229, 296, ⟨0, 3, false, true, false, 296, 296⟩⟩,
   ⟨297, 468, ⟨3, 7, false, true, false, 297, 297⟩⟩,
   ⟨469, 572, ⟨3, 7, false, false, false, 469, 469⟩⟩],
  [⟨158, 228, ⟨0, 2, true, true, false, 228, 228⟩⟩,
   ⟨229, 296, ⟨0, 2, false, true, false, 296, 296⟩⟩,
   ⟨297, 468, ⟨2, 7, false, true, false, 297, 297⟩⟩,
   ⟨469, 624, ⟨2, 7, false, false, false, 469, 469⟩⟩],
  [⟨211, 228, ⟨0, 2, true, true, false, 228, 228⟩⟩,
   ⟨229, 348, ⟨0, 2, false, true, false, 348, 348⟩⟩,
   ⟨349, 468, ⟨2, 7, false, true, false, 468, 468⟩⟩,
   ⟨469, 729, ⟨2, 7, false, false, false, 729, 729⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_297_lower : ConfigurationBounds 297 8243 161 := by
  apply configuration_of_cells 297 8243 161 data_297_lower
  decide +kernel

private def data_298_lower : Array (List Chunk) := #[
  [⟨1, 229, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨230, 244, ⟨0, 3, false, true, false, 230, 230⟩⟩,
   ⟨245, 450, ⟨3, 7, false, true, false, 245, 245⟩⟩,
   ⟨451, 520, ⟨3, 7, false, false, false, 451, 451⟩⟩],
  [⟨106, 229, ⟨0, 3, true, true, false, 229, 229⟩⟩,
   ⟨230, 297, ⟨0, 3, false, true, false, 297, 297⟩⟩,
   ⟨298, 450, ⟨3, 7, false, true, false, 298, 298⟩⟩,
   ⟨451, 573, ⟨3, 7, false, false, false, 451, 451⟩⟩],
  [⟨159, 229, ⟨0, 2, true, true, false, 229, 229⟩⟩,
   ⟨230, 297, ⟨0, 2, false, true, false, 297, 297⟩⟩,
   ⟨298, 450, ⟨2, 7, false, true, false, 298, 298⟩⟩,
   ⟨451, 626, ⟨2, 7, false, false, false, 451, 451⟩⟩],
  [⟨212, 229, ⟨0, 2, true, true, false, 229, 229⟩⟩,
   ⟨230, 350, ⟨0, 2, false, true, false, 350, 350⟩⟩,
   ⟨351, 450, ⟨2, 7, false, true, false, 450, 450⟩⟩,
   ⟨451, 731, ⟨2, 7, false, false, false, 731, 731⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_298_lower : ConfigurationBounds 298 8298 162 := by
  apply configuration_of_cells 298 8298 162 data_298_lower
  decide +kernel

private def data_299_lower : Array (List Chunk) := #[
  [⟨1, 230, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨231, 245, ⟨0, 3, false, true, false, 231, 231⟩⟩,
   ⟨246, 388, ⟨3, 7, false, true, false, 246, 246⟩⟩,
   ⟨389, 523, ⟨3, 7, false, false, false, 389, 389⟩⟩],
  [⟨106, 230, ⟨0, 3, true, true, false, 230, 230⟩⟩,
   ⟨231, 298, ⟨0, 3, false, true, false, 298, 298⟩⟩,
   ⟨299, 388, ⟨3, 7, false, true, false, 299, 299⟩⟩,
   ⟨389, 576, ⟨3, 7, false, false, false, 389, 389⟩⟩],
  [⟨159, 230, ⟨0, 2, true, true, false, 230, 230⟩⟩,
   ⟨231, 298, ⟨0, 2, false, true, false, 298, 298⟩⟩,
   ⟨299, 388, ⟨2, 7, false, true, false, 299, 299⟩⟩,
   ⟨389, 629, ⟨2, 7, false, false, false, 389, 389⟩⟩],
  [⟨212, 230, ⟨0, 2, true, true, false, 230, 230⟩⟩,
   ⟨231, 351, ⟨0, 2, false, true, false, 351, 351⟩⟩,
   ⟨352, 388, ⟨2, 7, false, true, false, 388, 388⟩⟩,
   ⟨389, 734, ⟨2, 7, false, false, false, 734, 734⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_299_lower : ConfigurationBounds 299 8353 162 := by
  apply configuration_of_cells 299 8353 162 data_299_lower
  decide +kernel

private def data_300_lower : Array (List Chunk) := #[
  [⟨1, 230, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨231, 246, ⟨0, 3, false, true, false, 231, 231⟩⟩,
   ⟨247, 511, ⟨3, 7, false, true, false, 247, 247⟩⟩,
   ⟨512, 526, ⟨3, 7, false, false, false, 512, 512⟩⟩],
  [⟨106, 230, ⟨0, 3, true, true, false, 230, 230⟩⟩,
   ⟨231, 299, ⟨0, 3, false, true, false, 299, 299⟩⟩,
   ⟨300, 511, ⟨3, 7, false, true, false, 300, 300⟩⟩,
   ⟨512, 579, ⟨3, 7, false, false, false, 512, 512⟩⟩],
  [⟨159, 230, ⟨0, 2, true, true, false, 230, 230⟩⟩,
   ⟨231, 299, ⟨0, 2, false, true, false, 299, 299⟩⟩,
   ⟨300, 511, ⟨2, 7, false, true, false, 300, 300⟩⟩,
   ⟨512, 632, ⟨2, 7, false, false, false, 512, 512⟩⟩],
  [⟨212, 230, ⟨0, 2, true, true, false, 230, 230⟩⟩,
   ⟨231, 352, ⟨0, 2, false, true, false, 352, 352⟩⟩,
   ⟨353, 511, ⟨2, 7, false, true, false, 511, 511⟩⟩,
   ⟨512, 737, ⟨2, 7, false, false, false, 737, 737⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_300_lower : ConfigurationBounds 300 8409 162 := by
  apply configuration_of_cells 300 8409 162 data_300_lower
  decide +kernel

private def data_301_lower : Array (List Chunk) := #[
  [⟨1, 231, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨232, 246, ⟨0, 3, false, true, false, 232, 232⟩⟩,
   ⟨247, 526, ⟨3, 7, false, true, false, 247, 247⟩⟩],
  [⟨107, 231, ⟨0, 3, true, true, false, 231, 231⟩⟩,
   ⟨232, 300, ⟨0, 3, false, true, false, 300, 300⟩⟩,
   ⟨301, 580, ⟨3, 7, false, true, false, 301, 301⟩⟩],
  [⟨160, 231, ⟨0, 2, true, true, false, 231, 231⟩⟩,
   ⟨232, 300, ⟨0, 2, false, true, false, 300, 300⟩⟩,
   ⟨301, 594, ⟨2, 7, false, true, false, 301, 301⟩⟩,
   ⟨595, 633, ⟨2, 7, false, false, false, 595, 595⟩⟩],
  [⟨214, 231, ⟨0, 2, true, true, false, 231, 231⟩⟩,
   ⟨232, 353, ⟨0, 2, false, true, false, 353, 353⟩⟩,
   ⟨354, 594, ⟨2, 7, false, true, false, 594, 594⟩⟩,
   ⟨595, 739, ⟨2, 7, false, false, false, 739, 739⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_301_lower : ConfigurationBounds 301 8465 163 := by
  apply configuration_of_cells 301 8465 163 data_301_lower
  decide +kernel

private def data_302_lower : Array (List Chunk) := #[
  [⟨1, 232, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨233, 247, ⟨0, 3, false, true, false, 233, 233⟩⟩,
   ⟨248, 409, ⟨3, 7, false, true, false, 248, 248⟩⟩,
   ⟨410, 527, ⟨3, 7, false, false, false, 410, 410⟩⟩],
  [⟨108, 232, ⟨0, 3, true, true, false, 232, 232⟩⟩,
   ⟨233, 301, ⟨0, 3, false, true, false, 301, 301⟩⟩,
   ⟨302, 409, ⟨3, 7, false, true, false, 302, 302⟩⟩,
   ⟨410, 581, ⟨3, 7, false, false, false, 410, 410⟩⟩],
  [⟨161, 232, ⟨0, 2, true, true, false, 232, 232⟩⟩,
   ⟨233, 301, ⟨0, 2, false, true, false, 301, 301⟩⟩,
   ⟨302, 409, ⟨2, 7, false, true, false, 302, 302⟩⟩,
   ⟨410, 634, ⟨2, 7, false, false, false, 410, 410⟩⟩],
  [⟨215, 232, ⟨0, 2, true, true, false, 232, 232⟩⟩,
   ⟨233, 354, ⟨0, 2, false, true, false, 354, 354⟩⟩,
   ⟨355, 409, ⟨2, 7, false, true, false, 409, 409⟩⟩,
   ⟨410, 741, ⟨2, 7, false, false, false, 741, 741⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_302_lower : ConfigurationBounds 302 8520 164 := by
  apply configuration_of_cells 302 8520 164 data_302_lower
  decide +kernel

private def data_303_lower : Array (List Chunk) := #[
  [⟨1, 233, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨234, 248, ⟨0, 3, false, true, false, 234, 234⟩⟩,
   ⟨249, 407, ⟨3, 7, false, true, false, 249, 249⟩⟩,
   ⟨408, 530, ⟨3, 7, false, false, false, 408, 408⟩⟩],
  [⟨108, 233, ⟨0, 3, true, true, false, 233, 233⟩⟩,
   ⟨234, 302, ⟨0, 3, false, true, false, 302, 302⟩⟩,
   ⟨303, 407, ⟨3, 7, false, true, false, 303, 303⟩⟩,
   ⟨408, 584, ⟨3, 7, false, false, false, 408, 408⟩⟩],
  [⟨161, 233, ⟨0, 2, true, true, false, 233, 233⟩⟩,
   ⟨234, 302, ⟨0, 2, false, true, false, 302, 302⟩⟩,
   ⟨303, 407, ⟨2, 7, false, true, false, 303, 303⟩⟩,
   ⟨408, 637, ⟨2, 7, false, false, false, 408, 408⟩⟩],
  [⟨215, 233, ⟨0, 2, true, true, false, 233, 233⟩⟩,
   ⟨234, 355, ⟨0, 2, false, true, false, 355, 355⟩⟩,
   ⟨356, 407, ⟨2, 7, false, true, false, 407, 407⟩⟩,
   ⟨408, 744, ⟨2, 7, false, false, false, 744, 744⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_303_lower : ConfigurationBounds 303 8576 164 := by
  apply configuration_of_cells 303 8576 164 data_303_lower
  decide +kernel

private def data_304_lower : Array (List Chunk) := #[
  [⟨1, 233, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨234, 249, ⟨0, 3, false, true, false, 234, 234⟩⟩,
   ⟨250, 533, ⟨3, 7, false, true, false, 250, 250⟩⟩],
  [⟨108, 233, ⟨0, 3, true, true, false, 233, 233⟩⟩,
   ⟨234, 303, ⟨0, 3, false, true, false, 303, 303⟩⟩,
   ⟨304, 587, ⟨3, 7, false, true, false, 304, 304⟩⟩],
  [⟨161, 233, ⟨0, 2, true, true, false, 233, 233⟩⟩,
   ⟨234, 303, ⟨0, 2, false, true, false, 303, 303⟩⟩,
   ⟨304, 593, ⟨2, 7, false, true, false, 304, 304⟩⟩,
   ⟨594, 640, ⟨2, 7, false, false, false, 594, 594⟩⟩],
  [⟨215, 233, ⟨0, 2, true, true, false, 233, 233⟩⟩,
   ⟨234, 356, ⟨0, 2, false, true, false, 356, 356⟩⟩,
   ⟨357, 593, ⟨2, 7, false, true, false, 593, 593⟩⟩,
   ⟨594, 747, ⟨2, 7, false, false, false, 747, 747⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_304_lower : ConfigurationBounds 304 8633 164 := by
  apply configuration_of_cells 304 8633 164 data_304_lower
  decide +kernel

private def data_305_lower : Array (List Chunk) := #[
  [⟨1, 234, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨235, 250, ⟨0, 3, false, true, false, 235, 235⟩⟩,
   ⟨251, 509, ⟨3, 7, false, true, false, 251, 251⟩⟩,
   ⟨510, 534, ⟨3, 7, false, false, false, 510, 510⟩⟩],
  [⟨108, 234, ⟨0, 3, true, true, false, 234, 234⟩⟩,
   ⟨235, 304, ⟨0, 3, false, true, false, 304, 304⟩⟩,
   ⟨305, 509, ⟨3, 7, false, true, false, 305, 305⟩⟩,
   ⟨510, 588, ⟨3, 7, false, false, false, 510, 510⟩⟩],
  [⟨162, 234, ⟨0, 2, true, true, false, 234, 234⟩⟩,
   ⟨235, 304, ⟨0, 2, false, true, false, 304, 304⟩⟩,
   ⟨305, 509, ⟨2, 7, false, true, false, 305, 305⟩⟩,
   ⟨510, 642, ⟨2, 7, false, false, false, 510, 510⟩⟩],
  [⟨216, 234, ⟨0, 2, true, true, false, 234, 234⟩⟩,
   ⟨235, 358, ⟨0, 2, false, true, false, 358, 358⟩⟩,
   ⟨359, 509, ⟨2, 7, false, true, false, 509, 509⟩⟩,
   ⟨510, 749, ⟨2, 7, false, false, false, 749, 749⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_305_lower : ConfigurationBounds 305 8689 165 := by
  apply configuration_of_cells 305 8689 165 data_305_lower
  decide +kernel

private def data_306_lower : Array (List Chunk) := #[
  [⟨1, 235, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨236, 250, ⟨0, 3, false, true, false, 236, 236⟩⟩,
   ⟨251, 382, ⟨3, 7, false, true, false, 251, 251⟩⟩,
   ⟨383, 534, ⟨3, 7, false, false, false, 383, 383⟩⟩],
  [⟨109, 235, ⟨0, 3, true, true, false, 235, 235⟩⟩,
   ⟨236, 305, ⟨0, 3, false, true, false, 305, 305⟩⟩,
   ⟨306, 382, ⟨3, 7, false, true, false, 306, 306⟩⟩,
   ⟨383, 589, ⟨3, 7, false, false, false, 383, 383⟩⟩],
  [⟨163, 235, ⟨0, 2, true, true, false, 235, 235⟩⟩,
   ⟨236, 305, ⟨0, 2, false, true, false, 305, 305⟩⟩,
   ⟨306, 382, ⟨2, 7, false, true, false, 306, 306⟩⟩,
   ⟨383, 643, ⟨2, 7, false, false, false, 383, 383⟩⟩],
  [⟨218, 235, ⟨0, 2, true, true, false, 235, 235⟩⟩,
   ⟨236, 359, ⟨0, 2, false, true, false, 359, 359⟩⟩,
   ⟨360, 382, ⟨2, 7, false, true, false, 382, 382⟩⟩,
   ⟨383, 751, ⟨2, 7, false, false, false, 751, 751⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_306_lower : ConfigurationBounds 306 8745 166 := by
  apply configuration_of_cells 306 8745 166 data_306_lower
  decide +kernel

private def data_307_lower : Array (List Chunk) := #[
  [⟨1, 236, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨237, 251, ⟨0, 3, false, true, false, 237, 237⟩⟩,
   ⟨252, 443, ⟨3, 7, false, true, false, 252, 252⟩⟩,
   ⟨444, 535, ⟨3, 7, false, false, false, 444, 444⟩⟩],
  [⟨110, 236, ⟨0, 3, true, true, false, 236, 236⟩⟩,
   ⟨237, 306, ⟨0, 3, false, true, false, 306, 306⟩⟩,
   ⟨307, 443, ⟨3, 7, false, true, false, 307, 307⟩⟩,
   ⟨444, 590, ⟨3, 7, false, false, false, 444, 444⟩⟩],
  [⟨164, 236, ⟨0, 2, true, true, false, 236, 236⟩⟩,
   ⟨237, 306, ⟨0, 2, false, true, false, 306, 306⟩⟩,
   ⟨307, 443, ⟨2, 7, false, true, false, 307, 307⟩⟩,
   ⟨444, 644, ⟨2, 7, false, false, false, 444, 444⟩⟩],
  [⟨219, 236, ⟨0, 2, true, true, false, 236, 236⟩⟩,
   ⟨237, 360, ⟨0, 2, false, true, false, 360, 360⟩⟩,
   ⟨361, 443, ⟨2, 7, false, true, false, 443, 443⟩⟩,
   ⟨444, 753, ⟨2, 7, false, false, false, 753, 753⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_307_lower : ConfigurationBounds 307 8802 167 := by
  apply configuration_of_cells 307 8802 167 data_307_lower
  decide +kernel

private def data_308_lower : Array (List Chunk) := #[
  [⟨1, 237, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨238, 252, ⟨0, 3, false, true, false, 238, 238⟩⟩,
   ⟨253, 461, ⟨3, 7, false, true, false, 253, 253⟩⟩,
   ⟨462, 538, ⟨3, 7, false, false, false, 462, 462⟩⟩],
  [⟨110, 237, ⟨0, 3, true, true, false, 237, 237⟩⟩,
   ⟨238, 307, ⟨0, 3, false, true, false, 307, 307⟩⟩,
   ⟨308, 461, ⟨3, 7, false, true, false, 308, 308⟩⟩,
   ⟨462, 593, ⟨3, 7, false, false, false, 462, 462⟩⟩],
  [⟨164, 237, ⟨0, 2, true, true, false, 237, 237⟩⟩,
   ⟨238, 307, ⟨0, 2, false, true, false, 307, 307⟩⟩,
   ⟨308, 461, ⟨2, 7, false, true, false, 308, 308⟩⟩,
   ⟨462, 647, ⟨2, 7, false, false, false, 462, 462⟩⟩],
  [⟨219, 237, ⟨0, 2, true, true, false, 237, 237⟩⟩,
   ⟨238, 361, ⟨0, 2, false, true, false, 361, 361⟩⟩,
   ⟨362, 461, ⟨2, 7, false, true, false, 461, 461⟩⟩,
   ⟨462, 756, ⟨2, 7, false, false, false, 756, 756⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_308_lower : ConfigurationBounds 308 8859 167 := by
  apply configuration_of_cells 308 8859 167 data_308_lower
  decide +kernel

private def data_309_lower : Array (List Chunk) := #[
  [⟨1, 238, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨239, 253, ⟨0, 3, false, true, false, 239, 239⟩⟩,
   ⟨254, 437, ⟨3, 7, false, true, false, 254, 254⟩⟩,
   ⟨438, 539, ⟨3, 7, false, false, false, 438, 438⟩⟩],
  [⟨110, 238, ⟨0, 3, true, true, false, 238, 238⟩⟩,
   ⟨239, 308, ⟨0, 3, false, true, false, 308, 308⟩⟩,
   ⟨309, 437, ⟨3, 7, false, true, false, 309, 309⟩⟩,
   ⟨438, 594, ⟨3, 7, false, false, false, 438, 438⟩⟩],
  [⟨165, 238, ⟨0, 2, true, true, false, 238, 238⟩⟩,
   ⟨239, 308, ⟨0, 2, false, true, false, 308, 308⟩⟩,
   ⟨309, 437, ⟨2, 7, false, true, false, 309, 309⟩⟩,
   ⟨438, 649, ⟨2, 7, false, false, false, 438, 438⟩⟩],
  [⟨220, 238, ⟨0, 2, true, true, false, 238, 238⟩⟩,
   ⟨239, 363, ⟨0, 2, false, true, false, 363, 363⟩⟩,
   ⟨364, 437, ⟨2, 7, false, true, false, 437, 437⟩⟩,
   ⟨438, 758, ⟨2, 7, false, false, false, 758, 758⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_309_lower : ConfigurationBounds 309 8916 168 := by
  apply configuration_of_cells 309 8916 168 data_309_lower
  decide +kernel

private def data_310_lower : Array (List Chunk) := #[
  [⟨1, 238, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨239, 254, ⟨0, 3, false, true, false, 239, 239⟩⟩,
   ⟨255, 542, ⟨3, 7, false, true, false, 255, 255⟩⟩],
  [⟨110, 238, ⟨0, 3, true, true, false, 238, 238⟩⟩,
   ⟨239, 309, ⟨0, 3, false, true, false, 309, 309⟩⟩,
   ⟨310, 597, ⟨3, 7, false, true, false, 310, 310⟩⟩],
  [⟨165, 238, ⟨0, 2, true, true, false, 238, 238⟩⟩,
   ⟨239, 309, ⟨0, 2, false, true, false, 309, 309⟩⟩,
   ⟨310, 602, ⟨2, 7, false, true, false, 310, 310⟩⟩,
   ⟨603, 652, ⟨2, 7, false, false, false, 603, 603⟩⟩],
  [⟨220, 238, ⟨0, 2, true, true, false, 238, 238⟩⟩,
   ⟨239, 364, ⟨0, 2, false, true, false, 364, 364⟩⟩,
   ⟨365, 602, ⟨2, 7, false, true, false, 602, 602⟩⟩,
   ⟨603, 761, ⟨2, 7, false, false, false, 761, 761⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_310_lower : ConfigurationBounds 310 8974 168 := by
  apply configuration_of_cells 310 8974 168 data_310_lower
  decide +kernel

private def data_311_lower : Array (List Chunk) := #[
  [⟨1, 239, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨240, 254, ⟨0, 3, false, true, false, 240, 240⟩⟩,
   ⟨255, 493, ⟨3, 7, false, true, false, 255, 255⟩⟩,
   ⟨494, 542, ⟨3, 7, false, false, false, 494, 494⟩⟩],
  [⟨111, 239, ⟨0, 3, true, true, false, 239, 239⟩⟩,
   ⟨240, 310, ⟨0, 3, false, true, false, 310, 310⟩⟩,
   ⟨311, 493, ⟨3, 7, false, true, false, 311, 311⟩⟩,
   ⟨494, 598, ⟨3, 7, false, false, false, 494, 494⟩⟩],
  [⟨166, 239, ⟨0, 2, true, true, false, 239, 239⟩⟩,
   ⟨240, 310, ⟨0, 2, false, true, false, 310, 310⟩⟩,
   ⟨311, 493, ⟨2, 7, false, true, false, 311, 311⟩⟩,
   ⟨494, 653, ⟨2, 7, false, false, false, 494, 494⟩⟩],
  [⟨222, 239, ⟨0, 2, true, true, false, 239, 239⟩⟩,
   ⟨240, 365, ⟨0, 2, false, true, false, 365, 365⟩⟩,
   ⟨366, 493, ⟨2, 7, false, true, false, 493, 493⟩⟩,
   ⟨494, 763, ⟨2, 7, false, false, false, 763, 763⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_311_lower : ConfigurationBounds 311 9031 169 := by
  apply configuration_of_cells 311 9031 169 data_311_lower
  decide +kernel

private def data_312_lower : Array (List Chunk) := #[
  [⟨1, 240, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨241, 255, ⟨0, 3, false, true, false, 241, 241⟩⟩,
   ⟨256, 545, ⟨3, 7, false, true, false, 256, 256⟩⟩],
  [⟨111, 240, ⟨0, 3, true, true, false, 240, 240⟩⟩,
   ⟨241, 311, ⟨0, 3, false, true, false, 311, 311⟩⟩,
   ⟨312, 573, ⟨3, 7, false, true, false, 312, 312⟩⟩,
   ⟨574, 601, ⟨3, 7, false, false, false, 574, 574⟩⟩],
  [⟨166, 240, ⟨0, 2, true, true, false, 240, 240⟩⟩,
   ⟨241, 311, ⟨0, 2, false, true, false, 311, 311⟩⟩,
   ⟨312, 573, ⟨2, 7, false, true, false, 312, 312⟩⟩,
   ⟨574, 656, ⟨2, 7, false, false, false, 574, 574⟩⟩],
  [⟨222, 240, ⟨0, 2, true, true, false, 240, 240⟩⟩,
   ⟨241, 366, ⟨0, 2, false, true, false, 366, 366⟩⟩,
   ⟨367, 573, ⟨2, 7, false, true, false, 573, 573⟩⟩,
   ⟨574, 766, ⟨2, 7, false, false, false, 766, 766⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_312_lower : ConfigurationBounds 312 9089 169 := by
  apply configuration_of_cells 312 9089 169 data_312_lower
  decide +kernel

private def data_313_lower : Array (List Chunk) := #[
  [⟨1, 240, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨241, 256, ⟨0, 3, false, true, false, 241, 241⟩⟩,
   ⟨257, 548, ⟨3, 7, false, true, false, 257, 257⟩⟩],
  [⟨111, 240, ⟨0, 3, true, true, false, 240, 240⟩⟩,
   ⟨241, 312, ⟨0, 3, false, true, false, 312, 312⟩⟩,
   ⟨313, 604, ⟨3, 7, false, true, false, 313, 313⟩⟩],
  [⟨166, 240, ⟨0, 2, true, true, false, 240, 240⟩⟩,
   ⟨241, 312, ⟨0, 2, false, true, false, 312, 312⟩⟩,
   ⟨313, 611, ⟨2, 7, false, true, false, 313, 313⟩⟩,
   ⟨612, 659, ⟨2, 7, false, false, false, 612, 612⟩⟩],
  [⟨222, 240, ⟨0, 2, true, true, false, 240, 240⟩⟩,
   ⟨241, 367, ⟨0, 2, false, true, false, 367, 367⟩⟩,
   ⟨368, 611, ⟨2, 7, false, true, false, 611, 611⟩⟩,
   ⟨612, 769, ⟨2, 7, false, false, false, 769, 769⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_313_lower : ConfigurationBounds 313 9147 169 := by
  apply configuration_of_cells 313 9147 169 data_313_lower
  decide +kernel

private def data_314_lower : Array (List Chunk) := #[
  [⟨1, 241, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨242, 257, ⟨0, 3, false, true, false, 242, 242⟩⟩,
   ⟨258, 549, ⟨3, 7, false, true, false, 258, 258⟩⟩],
  [⟨112, 241, ⟨0, 3, true, true, false, 241, 241⟩⟩,
   ⟨242, 313, ⟨0, 3, false, true, false, 313, 313⟩⟩,
   ⟨314, 605, ⟨3, 7, false, true, false, 314, 314⟩⟩],
  [⟨167, 241, ⟨0, 2, true, true, false, 241, 241⟩⟩,
   ⟨242, 313, ⟨0, 2, false, true, false, 313, 313⟩⟩,
   ⟨314, 607, ⟨2, 7, false, true, false, 314, 314⟩⟩,
   ⟨608, 660, ⟨2, 7, false, false, false, 608, 608⟩⟩],
  [⟨223, 241, ⟨0, 2, true, true, false, 241, 241⟩⟩,
   ⟨242, 368, ⟨0, 2, false, true, false, 368, 368⟩⟩,
   ⟨369, 607, ⟨2, 7, false, true, false, 607, 607⟩⟩,
   ⟨608, 771, ⟨2, 7, false, false, false, 771, 771⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_314_lower : ConfigurationBounds 314 9205 170 := by
  apply configuration_of_cells 314 9205 170 data_314_lower
  decide +kernel

private def data_315_lower : Array (List Chunk) := #[
  [⟨1, 242, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨243, 258, ⟨0, 3, false, true, false, 243, 243⟩⟩,
   ⟨259, 550, ⟨3, 7, false, true, false, 259, 259⟩⟩],
  [⟨112, 242, ⟨0, 3, true, true, false, 242, 242⟩⟩,
   ⟨243, 314, ⟨0, 3, false, true, false, 314, 314⟩⟩,
   ⟨315, 559, ⟨3, 7, false, true, false, 315, 315⟩⟩,
   ⟨560, 606, ⟨3, 7, false, false, false, 560, 560⟩⟩],
  [⟨168, 242, ⟨0, 2, true, true, false, 242, 242⟩⟩,
   ⟨243, 314, ⟨0, 2, false, true, false, 314, 314⟩⟩,
   ⟨315, 559, ⟨2, 7, false, true, false, 315, 315⟩⟩,
   ⟨560, 662, ⟨2, 7, false, false, false, 560, 560⟩⟩],
  [⟨224, 242, ⟨0, 2, true, true, false, 242, 242⟩⟩,
   ⟨243, 370, ⟨0, 2, false, true, false, 370, 370⟩⟩,
   ⟨371, 559, ⟨2, 7, false, true, false, 559, 559⟩⟩,
   ⟨560, 773, ⟨2, 7, false, false, false, 773, 773⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_315_lower : ConfigurationBounds 315 9263 171 := by
  apply configuration_of_cells 315 9263 171 data_315_lower
  decide +kernel

private def data_316_lower : Array (List Chunk) := #[
  [⟨1, 243, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨244, 259, ⟨0, 3, false, true, false, 244, 244⟩⟩,
   ⟨260, 466, ⟨3, 7, false, true, false, 260, 260⟩⟩,
   ⟨467, 553, ⟨3, 7, false, false, false, 467, 467⟩⟩],
  [⟨112, 243, ⟨0, 3, true, true, false, 243, 243⟩⟩,
   ⟨244, 315, ⟨0, 3, false, true, false, 315, 315⟩⟩,
   ⟨316, 466, ⟨3, 7, false, true, false, 316, 316⟩⟩,
   ⟨467, 609, ⟨3, 7, false, false, false, 467, 467⟩⟩],
  [⟨168, 243, ⟨0, 2, true, true, false, 243, 243⟩⟩,
   ⟨244, 315, ⟨0, 2, false, true, false, 315, 315⟩⟩,
   ⟨316, 466, ⟨2, 7, false, true, false, 316, 316⟩⟩,
   ⟨467, 665, ⟨2, 7, false, false, false, 467, 467⟩⟩],
  [⟨224, 243, ⟨0, 2, true, true, false, 243, 243⟩⟩,
   ⟨244, 371, ⟨0, 2, false, true, false, 371, 371⟩⟩,
   ⟨372, 466, ⟨2, 7, false, true, false, 466, 466⟩⟩,
   ⟨467, 776, ⟨2, 7, false, false, false, 776, 776⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_316_lower : ConfigurationBounds 316 9321 171 := by
  apply configuration_of_cells 316 9321 171 data_316_lower
  decide +kernel

private def data_317_lower : Array (List Chunk) := #[
  [⟨1, 244, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨245, 259, ⟨0, 3, false, true, false, 245, 245⟩⟩,
   ⟨260, 553, ⟨3, 7, false, true, false, 260, 260⟩⟩],
  [⟨113, 244, ⟨0, 3, true, true, false, 244, 244⟩⟩,
   ⟨245, 316, ⟨0, 3, false, true, false, 316, 316⟩⟩,
   ⟨317, 569, ⟨3, 7, false, true, false, 317, 317⟩⟩,
   ⟨570, 610, ⟨3, 7, false, false, false, 570, 570⟩⟩],
  [⟨169, 244, ⟨0, 2, true, true, false, 244, 244⟩⟩,
   ⟨245, 316, ⟨0, 2, false, true, false, 316, 316⟩⟩,
   ⟨317, 569, ⟨2, 7, false, true, false, 317, 317⟩⟩,
   ⟨570, 666, ⟨2, 7, false, false, false, 570, 570⟩⟩],
  [⟨226, 244, ⟨0, 2, true, true, false, 244, 244⟩⟩,
   ⟨245, 372, ⟨0, 2, false, true, false, 372, 372⟩⟩,
   ⟨373, 569, ⟨2, 7, false, true, false, 569, 569⟩⟩,
   ⟨570, 778, ⟨2, 7, false, false, false, 778, 778⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_317_lower : ConfigurationBounds 317 9380 172 := by
  apply configuration_of_cells 317 9380 172 data_317_lower
  decide +kernel

private def data_318_lower : Array (List Chunk) := #[
  [⟨1, 244, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨245, 260, ⟨0, 3, false, true, false, 245, 245⟩⟩,
   ⟨261, 556, ⟨3, 7, false, true, false, 261, 261⟩⟩],
  [⟨113, 244, ⟨0, 3, true, true, false, 244, 244⟩⟩,
   ⟨245, 317, ⟨0, 3, false, true, false, 317, 317⟩⟩,
   ⟨318, 613, ⟨3, 7, false, true, false, 318, 318⟩⟩],
  [⟨169, 244, ⟨0, 2, true, true, false, 244, 244⟩⟩,
   ⟨245, 317, ⟨0, 2, false, true, false, 317, 317⟩⟩,
   ⟨318, 627, ⟨2, 7, false, true, false, 318, 318⟩⟩,
   ⟨628, 669, ⟨2, 7, false, false, false, 628, 628⟩⟩],
  [⟨226, 244, ⟨0, 2, true, true, false, 244, 244⟩⟩,
   ⟨245, 373, ⟨0, 2, false, true, false, 373, 373⟩⟩,
   ⟨374, 627, ⟨2, 7, false, true, false, 627, 627⟩⟩,
   ⟨628, 781, ⟨2, 7, false, false, false, 781, 781⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_318_lower : ConfigurationBounds 318 9439 172 := by
  apply configuration_of_cells 318 9439 172 data_318_lower
  decide +kernel

private def data_319_lower : Array (List Chunk) := #[
  [⟨1, 245, ⟨0, 3, true, true, false, 1, 1⟩⟩,
   ⟨246, 261, ⟨0, 3, false, true, false, 246, 246⟩⟩,
   ⟨262, 402, ⟨3, 7, false, true, false, 262, 262⟩⟩,
   ⟨403, 557, ⟨3, 7, false, false, false, 403, 403⟩⟩],
  [⟨114, 245, ⟨0, 3, true, true, false, 245, 245⟩⟩,
   ⟨246, 318, ⟨0, 3, false, true, false, 318, 318⟩⟩,
   ⟨319, 402, ⟨3, 7, false, true, false, 319, 319⟩⟩,
   ⟨403, 614, ⟨3, 7, false, false, false, 403, 403⟩⟩],
  [⟨170, 245, ⟨0, 2, true, true, false, 245, 245⟩⟩,
   ⟨246, 318, ⟨0, 2, false, true, false, 318, 318⟩⟩,
   ⟨319, 402, ⟨2, 7, false, true, false, 319, 319⟩⟩,
   ⟨403, 670, ⟨2, 7, false, false, false, 403, 403⟩⟩],
  [⟨227, 245, ⟨0, 2, true, true, false, 245, 245⟩⟩,
   ⟨246, 374, ⟨0, 2, false, true, false, 374, 374⟩⟩,
   ⟨375, 402, ⟨2, 7, false, true, false, 402, 402⟩⟩,
   ⟨403, 783, ⟨2, 7, false, false, false, 783, 783⟩⟩]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_319_lower : ConfigurationBounds 319 9497 173 := by
  apply configuration_of_cells 319 9497 173 data_319_lower
  decide +kernel

end Quartic.MarkedHullCertificate
