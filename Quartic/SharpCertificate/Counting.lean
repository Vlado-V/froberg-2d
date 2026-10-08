import Quartic.SharpCertificate.Counting.Data

/-! Kernel-verified totals, assembled from bounded per-configuration counts. -/

namespace Quartic.SharpCertificate

open Quartic.FiniteCounts Quartic.ProfileCertificate

def countRecords : Array (ℕ × ℕ) := #[
  (8254, 432), (8356, 446), (8726, 458), (8808, 475), (9096, 461), (9198, 483), (9466, 455), (9588, 466),
  (9978, 424), (10080, 430), (10490, 509), (10572, 527), (11002, 531), (11064, 549), (11310, 468), (11432, 474),
  (11862, 530), (11964, 547), (12292, 486), (12414, 496), (12966, 579), (13028, 597), (13436, 579), (13518, 601),
  (14008, 601), (14070, 623), (14498, 568), (14580, 570), (15090, 627), (15152, 645), (15600, 619), (15682, 628),
  (16212, 610), (16274, 620), (16742, 632), (16824, 634), (17374, 673), (17436, 690), (17924, 582), (18006, 592),
  (18576, 696), (18638, 717), (19146, 684), (19228, 686), (19818, 692), (19880, 694), (20490, 736), (20532, 742),
  (21100, 745), (21162, 767), (21792, 730), (21834, 736), (22422, 676), (22484, 682), (23134, 793), (23176, 811),
  (23784, 686), (23846, 696), (24516, 754), (24558, 764), (25248, 837), (25270, 859), (25938, 792), (25980, 798),
  (26628, 754), (26690, 764), (27400, 766), (27442, 776), (28110, 816), (28172, 818), (28902, 889), (28944, 907),
  (29632, 810), (29694, 816), (30486, 933), (30488, 951), (31256, 933), (31278, 955), (32068, 955), (32070, 977),
  (32858, 860), (32880, 862), (33690, 981), (33692, 990), (34500, 902), (34522, 912), (35310, 864), (35352, 870),
  (36182, 880), (36204, 886), (37012, 938), (37054, 948), (37904, 1029), (37926, 1051), (38796, 946), (38796, 946),
  (39688, 1073), (39670, 1095), (40578, 1077), (40580, 1095), (41490, 1099), (41472, 1117), (42400, 1010), (42402, 1016),
  (43332, 1121), (43314, 1143), (44262, 1072), (44264, 1078), (45192, 1030), (45214, 1040), (46164, 1054), (46166, 1060),
  (47136, 1130), (47118, 1136), (48108, 1191), (48070, 1213), (49098, 1144), (49080, 1150), (50088, 1078), (50090, 1084),
  (51100, 1074), (51082, 1084), (52110, 1124), (52112, 1126), (53142, 1236), (53124, 1238), (54172, 1078), (54174, 1088),
  (55224, 1265), (55206, 1287), (56276, 1281), (56238, 1288), (57346, 1291), (57328, 1306), (58418, 1313), (58380, 1331),
  (59508, 1210), (59490, 1216), (60600, 1335), (60562, 1357), (61692, 1357), (61634, 1367), (62822, 1361), (62784, 1364),
  (63934, 1383), (63876, 1401), (65084, 1198), (65046, 1208), (66216, 1393), (66158, 1400), (67386, 1296), (67348, 1298),
  (68556, 1258), (68538, 1264), (69728, 1294), (69690, 1304), (70900, 1398), (70842, 1404), (72072, 1475), (71994, 1497),
  (73302, 1440), (73244, 1442), (74532, 1370), (74494, 1376), (75744, 1374), (75686, 1384), (76956, 1454), (76878, 1460),
  (78226, 1527), (78168, 1545), (79458, 1428), (79380, 1434), (80748, 1322), (80690, 1332), (82000, 1571), (81922, 1593),
  (83310, 1336), (83252, 1342)
]

def expectedCounts (m : ℕ) (upper : Bool) : ℕ × ℕ :=
  (countRecords[(m - 41) * 2 + if upper then 1 else 0]?).getD (0, 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every expected record is linked to the actual edge checker and source intervals. -/
theorem all_configuration_counts (index : Fin 89) (upper : Bool) :
    let m := (index : ℕ) + 41
    configurationValueCount m (mixedCount m upper) = (expectedCounts m upper).1 ∧
      configurationIntervalCount m (upperEndpoint m) (mixedCount m upper) =
        (expectedCounts m upper).2 := by
  fin_cases index <;> cases upper
  · exact configuration_counts_41_lower
  · exact configuration_counts_41_upper
  · exact configuration_counts_42_lower
  · exact configuration_counts_42_upper
  · exact configuration_counts_43_lower
  · exact configuration_counts_43_upper
  · exact configuration_counts_44_lower
  · exact configuration_counts_44_upper
  · exact configuration_counts_45_lower
  · exact configuration_counts_45_upper
  · exact configuration_counts_46_lower
  · exact configuration_counts_46_upper
  · exact configuration_counts_47_lower
  · exact configuration_counts_47_upper
  · exact configuration_counts_48_lower
  · exact configuration_counts_48_upper
  · exact configuration_counts_49_lower
  · exact configuration_counts_49_upper
  · exact configuration_counts_50_lower
  · exact configuration_counts_50_upper
  · exact configuration_counts_51_lower
  · exact configuration_counts_51_upper
  · exact configuration_counts_52_lower
  · exact configuration_counts_52_upper
  · exact configuration_counts_53_lower
  · exact configuration_counts_53_upper
  · exact configuration_counts_54_lower
  · exact configuration_counts_54_upper
  · exact configuration_counts_55_lower
  · exact configuration_counts_55_upper
  · exact configuration_counts_56_lower
  · exact configuration_counts_56_upper
  · exact configuration_counts_57_lower
  · exact configuration_counts_57_upper
  · exact configuration_counts_58_lower
  · exact configuration_counts_58_upper
  · exact configuration_counts_59_lower
  · exact configuration_counts_59_upper
  · exact configuration_counts_60_lower
  · exact configuration_counts_60_upper
  · exact configuration_counts_61_lower
  · exact configuration_counts_61_upper
  · exact configuration_counts_62_lower
  · exact configuration_counts_62_upper
  · exact configuration_counts_63_lower
  · exact configuration_counts_63_upper
  · exact configuration_counts_64_lower
  · exact configuration_counts_64_upper
  · exact configuration_counts_65_lower
  · exact configuration_counts_65_upper
  · exact configuration_counts_66_lower
  · exact configuration_counts_66_upper
  · exact configuration_counts_67_lower
  · exact configuration_counts_67_upper
  · exact configuration_counts_68_lower
  · exact configuration_counts_68_upper
  · exact configuration_counts_69_lower
  · exact configuration_counts_69_upper
  · exact configuration_counts_70_lower
  · exact configuration_counts_70_upper
  · exact configuration_counts_71_lower
  · exact configuration_counts_71_upper
  · exact configuration_counts_72_lower
  · exact configuration_counts_72_upper
  · exact configuration_counts_73_lower
  · exact configuration_counts_73_upper
  · exact configuration_counts_74_lower
  · exact configuration_counts_74_upper
  · exact configuration_counts_75_lower
  · exact configuration_counts_75_upper
  · exact configuration_counts_76_lower
  · exact configuration_counts_76_upper
  · exact configuration_counts_77_lower
  · exact configuration_counts_77_upper
  · exact configuration_counts_78_lower
  · exact configuration_counts_78_upper
  · exact configuration_counts_79_lower
  · exact configuration_counts_79_upper
  · exact configuration_counts_80_lower
  · exact configuration_counts_80_upper
  · exact configuration_counts_81_lower
  · exact configuration_counts_81_upper
  · exact configuration_counts_82_lower
  · exact configuration_counts_82_upper
  · exact configuration_counts_83_lower
  · exact configuration_counts_83_upper
  · exact configuration_counts_84_lower
  · exact configuration_counts_84_upper
  · exact configuration_counts_85_lower
  · exact configuration_counts_85_upper
  · exact configuration_counts_86_lower
  · exact configuration_counts_86_upper
  · exact configuration_counts_87_lower
  · exact configuration_counts_87_upper
  · exact configuration_counts_88_lower
  · exact configuration_counts_88_upper
  · exact configuration_counts_89_lower
  · exact configuration_counts_89_upper
  · exact configuration_counts_90_lower
  · exact configuration_counts_90_upper
  · exact configuration_counts_91_lower
  · exact configuration_counts_91_upper
  · exact configuration_counts_92_lower
  · exact configuration_counts_92_upper
  · exact configuration_counts_93_lower
  · exact configuration_counts_93_upper
  · exact configuration_counts_94_lower
  · exact configuration_counts_94_upper
  · exact configuration_counts_95_lower
  · exact configuration_counts_95_upper
  · exact configuration_counts_96_lower
  · exact configuration_counts_96_upper
  · exact configuration_counts_97_lower
  · exact configuration_counts_97_upper
  · exact configuration_counts_98_lower
  · exact configuration_counts_98_upper
  · exact configuration_counts_99_lower
  · exact configuration_counts_99_upper
  · exact configuration_counts_100_lower
  · exact configuration_counts_100_upper
  · exact configuration_counts_101_lower
  · exact configuration_counts_101_upper
  · exact configuration_counts_102_lower
  · exact configuration_counts_102_upper
  · exact configuration_counts_103_lower
  · exact configuration_counts_103_upper
  · exact configuration_counts_104_lower
  · exact configuration_counts_104_upper
  · exact configuration_counts_105_lower
  · exact configuration_counts_105_upper
  · exact configuration_counts_106_lower
  · exact configuration_counts_106_upper
  · exact configuration_counts_107_lower
  · exact configuration_counts_107_upper
  · exact configuration_counts_108_lower
  · exact configuration_counts_108_upper
  · exact configuration_counts_109_lower
  · exact configuration_counts_109_upper
  · exact configuration_counts_110_lower
  · exact configuration_counts_110_upper
  · exact configuration_counts_111_lower
  · exact configuration_counts_111_upper
  · exact configuration_counts_112_lower
  · exact configuration_counts_112_upper
  · exact configuration_counts_113_lower
  · exact configuration_counts_113_upper
  · exact configuration_counts_114_lower
  · exact configuration_counts_114_upper
  · exact configuration_counts_115_lower
  · exact configuration_counts_115_upper
  · exact configuration_counts_116_lower
  · exact configuration_counts_116_upper
  · exact configuration_counts_117_lower
  · exact configuration_counts_117_upper
  · exact configuration_counts_118_lower
  · exact configuration_counts_118_upper
  · exact configuration_counts_119_lower
  · exact configuration_counts_119_upper
  · exact configuration_counts_120_lower
  · exact configuration_counts_120_upper
  · exact configuration_counts_121_lower
  · exact configuration_counts_121_upper
  · exact configuration_counts_122_lower
  · exact configuration_counts_122_upper
  · exact configuration_counts_123_lower
  · exact configuration_counts_123_upper
  · exact configuration_counts_124_lower
  · exact configuration_counts_124_upper
  · exact configuration_counts_125_lower
  · exact configuration_counts_125_upper
  · exact configuration_counts_126_lower
  · exact configuration_counts_126_upper
  · exact configuration_counts_127_lower
  · exact configuration_counts_127_upper
  · exact configuration_counts_128_lower
  · exact configuration_counts_128_upper
  · exact configuration_counts_129_lower
  · exact configuration_counts_129_upper

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The finite proof covers 89,988 indexed core/edge pairs. -/
theorem total_edge_count :
    rangeTotal (fun m upper => configurationEdgeCount (mixedCount m upper)) = 89988 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Those edge domains contain 7,023,720 integer evaluations before compression. -/
theorem total_integer_edge_value_count :
    rangeTotal (fun m upper => configurationValueCount m (mixedCount m upper)) = 7023720 := by
  have h : rangeTotal (fun m upper => configurationValueCount m (mixedCount m upper)) =
      rangeTotal (fun m upper => (expectedCounts m upper).1) := by
    unfold rangeTotal
    apply congrArg List.sum
    apply List.map_congr_left
    intro index hindex
    have hlo := (all_configuration_counts ⟨index, List.mem_range.mp hindex⟩ false).1
    have hhi := (all_configuration_counts ⟨index, List.mem_range.mp hindex⟩ true).1
    exact congrArg₂ Nat.add hlo hhi
  rw [h]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The actual certificate algorithm uses 171,859 intervals. -/
theorem total_interval_count :
    rangeTotal (fun m upper => configurationIntervalCount m (upperEndpoint m) (mixedCount m upper)) =
      171859 := by
  have h : rangeTotal (fun m upper => configurationIntervalCount m (upperEndpoint m) (mixedCount m upper)) =
      rangeTotal (fun m upper => (expectedCounts m upper).2) := by
    unfold rangeTotal
    apply congrArg List.sum
    apply List.map_congr_left
    intro index hindex
    have hlo := (all_configuration_counts ⟨index, List.mem_range.mp hindex⟩ false).2
    have hhi := (all_configuration_counts ⟨index, List.mem_range.mp hindex⟩ true).2
    exact congrArg₂ Nat.add hlo hhi
  rw [h]
  decide +kernel

end Quartic.SharpCertificate
