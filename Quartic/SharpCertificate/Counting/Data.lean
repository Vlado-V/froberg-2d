import Quartic.SharpCertificate.Counting.Core

/-! Bounded kernel checks of the actual counts in each configuration. -/

namespace Quartic.SharpCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_41_lower :
    configurationValueCount 41 20 = 8254 ∧
      configurationIntervalCount 41 176 20 = 432 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_41_upper :
    configurationValueCount 41 21 = 8356 ∧
      configurationIntervalCount 41 176 21 = 446 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_42_lower :
    configurationValueCount 42 21 = 8726 ∧
      configurationIntervalCount 42 184 21 = 458 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_42_upper :
    configurationValueCount 42 22 = 8808 ∧
      configurationIntervalCount 42 184 22 = 475 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_43_lower :
    configurationValueCount 43 21 = 9096 ∧
      configurationIntervalCount 43 192 21 = 461 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_43_upper :
    configurationValueCount 43 22 = 9198 ∧
      configurationIntervalCount 43 192 22 = 483 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_44_lower :
    configurationValueCount 44 21 = 9466 ∧
      configurationIntervalCount 44 201 21 = 455 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_44_upper :
    configurationValueCount 44 22 = 9588 ∧
      configurationIntervalCount 44 201 22 = 466 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_45_lower :
    configurationValueCount 45 22 = 9978 ∧
      configurationIntervalCount 45 210 22 = 424 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_45_upper :
    configurationValueCount 45 23 = 10080 ∧
      configurationIntervalCount 45 210 23 = 430 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_46_lower :
    configurationValueCount 46 23 = 10490 ∧
      configurationIntervalCount 46 218 23 = 509 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_46_upper :
    configurationValueCount 46 24 = 10572 ∧
      configurationIntervalCount 46 218 24 = 527 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_47_lower :
    configurationValueCount 47 24 = 11002 ∧
      configurationIntervalCount 47 227 24 = 531 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_47_upper :
    configurationValueCount 47 25 = 11064 ∧
      configurationIntervalCount 47 227 25 = 549 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_48_lower :
    configurationValueCount 48 23 = 11310 ∧
      configurationIntervalCount 48 237 23 = 468 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_48_upper :
    configurationValueCount 48 24 = 11432 ∧
      configurationIntervalCount 48 237 24 = 474 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_49_lower :
    configurationValueCount 49 24 = 11862 ∧
      configurationIntervalCount 49 246 24 = 530 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_49_upper :
    configurationValueCount 49 25 = 11964 ∧
      configurationIntervalCount 49 246 25 = 547 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_50_lower :
    configurationValueCount 50 24 = 12292 ∧
      configurationIntervalCount 50 256 24 = 486 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_50_upper :
    configurationValueCount 50 25 = 12414 ∧
      configurationIntervalCount 50 256 25 = 496 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_51_lower :
    configurationValueCount 51 26 = 12966 ∧
      configurationIntervalCount 51 265 26 = 579 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_51_upper :
    configurationValueCount 51 27 = 13028 ∧
      configurationIntervalCount 51 265 27 = 597 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_52_lower :
    configurationValueCount 52 26 = 13436 ∧
      configurationIntervalCount 52 275 26 = 579 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_52_upper :
    configurationValueCount 52 27 = 13518 ∧
      configurationIntervalCount 52 275 27 = 601 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_53_lower :
    configurationValueCount 53 27 = 14008 ∧
      configurationIntervalCount 53 285 27 = 601 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_53_upper :
    configurationValueCount 53 28 = 14070 ∧
      configurationIntervalCount 53 285 28 = 623 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_54_lower :
    configurationValueCount 54 27 = 14498 ∧
      configurationIntervalCount 54 296 27 = 568 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_54_upper :
    configurationValueCount 54 28 = 14580 ∧
      configurationIntervalCount 54 296 28 = 570 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_55_lower :
    configurationValueCount 55 28 = 15090 ∧
      configurationIntervalCount 55 306 28 = 627 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_55_upper :
    configurationValueCount 55 29 = 15152 ∧
      configurationIntervalCount 55 306 29 = 645 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_56_lower :
    configurationValueCount 56 28 = 15600 ∧
      configurationIntervalCount 56 317 28 = 619 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_56_upper :
    configurationValueCount 56 29 = 15682 ∧
      configurationIntervalCount 56 317 29 = 628 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_57_lower :
    configurationValueCount 57 29 = 16212 ∧
      configurationIntervalCount 57 328 29 = 610 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_57_upper :
    configurationValueCount 57 30 = 16274 ∧
      configurationIntervalCount 57 328 30 = 620 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_58_lower :
    configurationValueCount 58 29 = 16742 ∧
      configurationIntervalCount 58 339 29 = 632 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_58_upper :
    configurationValueCount 58 30 = 16824 ∧
      configurationIntervalCount 58 339 30 = 634 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_59_lower :
    configurationValueCount 59 30 = 17374 ∧
      configurationIntervalCount 59 350 30 = 673 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_59_upper :
    configurationValueCount 59 31 = 17436 ∧
      configurationIntervalCount 59 350 31 = 690 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_60_lower :
    configurationValueCount 60 30 = 17924 ∧
      configurationIntervalCount 60 362 30 = 582 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_60_upper :
    configurationValueCount 60 31 = 18006 ∧
      configurationIntervalCount 60 362 31 = 592 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_61_lower :
    configurationValueCount 61 31 = 18576 ∧
      configurationIntervalCount 61 373 31 = 696 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_61_upper :
    configurationValueCount 61 32 = 18638 ∧
      configurationIntervalCount 61 373 32 = 717 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_62_lower :
    configurationValueCount 62 31 = 19146 ∧
      configurationIntervalCount 62 385 31 = 684 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_62_upper :
    configurationValueCount 62 32 = 19228 ∧
      configurationIntervalCount 62 385 32 = 686 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_63_lower :
    configurationValueCount 63 32 = 19818 ∧
      configurationIntervalCount 63 397 32 = 692 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_63_upper :
    configurationValueCount 63 33 = 19880 ∧
      configurationIntervalCount 63 397 33 = 694 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_64_lower :
    configurationValueCount 64 33 = 20490 ∧
      configurationIntervalCount 64 409 33 = 736 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_64_upper :
    configurationValueCount 64 34 = 20532 ∧
      configurationIntervalCount 64 409 34 = 742 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_65_lower :
    configurationValueCount 65 33 = 21100 ∧
      configurationIntervalCount 65 421 33 = 745 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_65_upper :
    configurationValueCount 65 34 = 21162 ∧
      configurationIntervalCount 65 421 34 = 767 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_66_lower :
    configurationValueCount 66 34 = 21792 ∧
      configurationIntervalCount 66 434 34 = 730 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_66_upper :
    configurationValueCount 66 35 = 21834 ∧
      configurationIntervalCount 66 434 35 = 736 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_67_lower :
    configurationValueCount 67 34 = 22422 ∧
      configurationIntervalCount 67 447 34 = 676 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_67_upper :
    configurationValueCount 67 35 = 22484 ∧
      configurationIntervalCount 67 447 35 = 682 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_68_lower :
    configurationValueCount 68 35 = 23134 ∧
      configurationIntervalCount 68 459 35 = 793 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_68_upper :
    configurationValueCount 68 36 = 23176 ∧
      configurationIntervalCount 68 459 36 = 811 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_69_lower :
    configurationValueCount 69 35 = 23784 ∧
      configurationIntervalCount 69 473 35 = 686 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_69_upper :
    configurationValueCount 69 36 = 23846 ∧
      configurationIntervalCount 69 473 36 = 696 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_70_lower :
    configurationValueCount 70 36 = 24516 ∧
      configurationIntervalCount 70 486 36 = 754 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_70_upper :
    configurationValueCount 70 37 = 24558 ∧
      configurationIntervalCount 70 486 37 = 764 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_71_lower :
    configurationValueCount 71 37 = 25248 ∧
      configurationIntervalCount 71 499 37 = 837 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_71_upper :
    configurationValueCount 71 38 = 25270 ∧
      configurationIntervalCount 71 499 38 = 859 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_72_lower :
    configurationValueCount 72 37 = 25938 ∧
      configurationIntervalCount 72 513 37 = 792 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_72_upper :
    configurationValueCount 72 38 = 25980 ∧
      configurationIntervalCount 72 513 38 = 798 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_73_lower :
    configurationValueCount 73 37 = 26628 ∧
      configurationIntervalCount 73 527 37 = 754 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_73_upper :
    configurationValueCount 73 38 = 26690 ∧
      configurationIntervalCount 73 527 38 = 764 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_74_lower :
    configurationValueCount 74 38 = 27400 ∧
      configurationIntervalCount 74 541 38 = 766 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_74_upper :
    configurationValueCount 74 39 = 27442 ∧
      configurationIntervalCount 74 541 39 = 776 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_75_lower :
    configurationValueCount 75 38 = 28110 ∧
      configurationIntervalCount 75 555 38 = 816 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_75_upper :
    configurationValueCount 75 39 = 28172 ∧
      configurationIntervalCount 75 555 39 = 818 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_76_lower :
    configurationValueCount 76 39 = 28902 ∧
      configurationIntervalCount 76 569 39 = 889 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_76_upper :
    configurationValueCount 76 40 = 28944 ∧
      configurationIntervalCount 76 569 40 = 907 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_77_lower :
    configurationValueCount 77 39 = 29632 ∧
      configurationIntervalCount 77 584 39 = 810 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_77_upper :
    configurationValueCount 77 40 = 29694 ∧
      configurationIntervalCount 77 584 40 = 816 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_78_lower :
    configurationValueCount 78 41 = 30486 ∧
      configurationIntervalCount 78 598 41 = 933 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_78_upper :
    configurationValueCount 78 42 = 30488 ∧
      configurationIntervalCount 78 598 42 = 951 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_79_lower :
    configurationValueCount 79 41 = 31256 ∧
      configurationIntervalCount 79 613 41 = 933 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_79_upper :
    configurationValueCount 79 42 = 31278 ∧
      configurationIntervalCount 79 613 42 = 955 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_80_lower :
    configurationValueCount 80 42 = 32068 ∧
      configurationIntervalCount 80 628 42 = 955 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_80_upper :
    configurationValueCount 80 43 = 32070 ∧
      configurationIntervalCount 80 628 43 = 977 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_81_lower :
    configurationValueCount 81 42 = 32858 ∧
      configurationIntervalCount 81 644 42 = 860 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_81_upper :
    configurationValueCount 81 43 = 32880 ∧
      configurationIntervalCount 81 644 43 = 862 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_82_lower :
    configurationValueCount 82 43 = 33690 ∧
      configurationIntervalCount 82 659 43 = 981 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_82_upper :
    configurationValueCount 82 44 = 33692 ∧
      configurationIntervalCount 82 659 44 = 990 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_83_lower :
    configurationValueCount 83 43 = 34500 ∧
      configurationIntervalCount 83 675 43 = 902 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_83_upper :
    configurationValueCount 83 44 = 34522 ∧
      configurationIntervalCount 83 675 44 = 912 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_84_lower :
    configurationValueCount 84 43 = 35310 ∧
      configurationIntervalCount 84 691 43 = 864 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_84_upper :
    configurationValueCount 84 44 = 35352 ∧
      configurationIntervalCount 84 691 44 = 870 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_85_lower :
    configurationValueCount 85 44 = 36182 ∧
      configurationIntervalCount 85 707 44 = 880 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_85_upper :
    configurationValueCount 85 45 = 36204 ∧
      configurationIntervalCount 85 707 45 = 886 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_86_lower :
    configurationValueCount 86 44 = 37012 ∧
      configurationIntervalCount 86 723 44 = 938 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_86_upper :
    configurationValueCount 86 45 = 37054 ∧
      configurationIntervalCount 86 723 45 = 948 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_87_lower :
    configurationValueCount 87 45 = 37904 ∧
      configurationIntervalCount 87 739 45 = 1029 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_87_upper :
    configurationValueCount 87 46 = 37926 ∧
      configurationIntervalCount 87 739 46 = 1051 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_88_lower :
    configurationValueCount 88 46 = 38796 ∧
      configurationIntervalCount 88 756 46 = 946 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_88_upper :
    configurationValueCount 88 46 = 38796 ∧
      configurationIntervalCount 88 756 46 = 946 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_89_lower :
    configurationValueCount 89 47 = 39688 ∧
      configurationIntervalCount 89 772 47 = 1073 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_89_upper :
    configurationValueCount 89 48 = 39670 ∧
      configurationIntervalCount 89 772 48 = 1095 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_90_lower :
    configurationValueCount 90 47 = 40578 ∧
      configurationIntervalCount 90 789 47 = 1077 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_90_upper :
    configurationValueCount 90 48 = 40580 ∧
      configurationIntervalCount 90 789 48 = 1095 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_91_lower :
    configurationValueCount 91 48 = 41490 ∧
      configurationIntervalCount 91 806 48 = 1099 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_91_upper :
    configurationValueCount 91 49 = 41472 ∧
      configurationIntervalCount 91 806 49 = 1117 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_92_lower :
    configurationValueCount 92 48 = 42400 ∧
      configurationIntervalCount 92 824 48 = 1010 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_92_upper :
    configurationValueCount 92 49 = 42402 ∧
      configurationIntervalCount 92 824 49 = 1016 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_93_lower :
    configurationValueCount 93 49 = 43332 ∧
      configurationIntervalCount 93 841 49 = 1121 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_93_upper :
    configurationValueCount 93 50 = 43314 ∧
      configurationIntervalCount 93 841 50 = 1143 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_94_lower :
    configurationValueCount 94 49 = 44262 ∧
      configurationIntervalCount 94 859 49 = 1072 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_94_upper :
    configurationValueCount 94 50 = 44264 ∧
      configurationIntervalCount 94 859 50 = 1078 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_95_lower :
    configurationValueCount 95 49 = 45192 ∧
      configurationIntervalCount 95 877 49 = 1030 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_95_upper :
    configurationValueCount 95 50 = 45214 ∧
      configurationIntervalCount 95 877 50 = 1040 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_96_lower :
    configurationValueCount 96 50 = 46164 ∧
      configurationIntervalCount 96 895 50 = 1054 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_96_upper :
    configurationValueCount 96 51 = 46166 ∧
      configurationIntervalCount 96 895 51 = 1060 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_97_lower :
    configurationValueCount 97 51 = 47136 ∧
      configurationIntervalCount 97 913 51 = 1130 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_97_upper :
    configurationValueCount 97 52 = 47118 ∧
      configurationIntervalCount 97 913 52 = 1136 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_98_lower :
    configurationValueCount 98 52 = 48108 ∧
      configurationIntervalCount 98 931 52 = 1191 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_98_upper :
    configurationValueCount 98 53 = 48070 ∧
      configurationIntervalCount 98 931 53 = 1213 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_99_lower :
    configurationValueCount 99 52 = 49098 ∧
      configurationIntervalCount 99 950 52 = 1144 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_99_upper :
    configurationValueCount 99 53 = 49080 ∧
      configurationIntervalCount 99 950 53 = 1150 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_100_lower :
    configurationValueCount 100 52 = 50088 ∧
      configurationIntervalCount 100 969 52 = 1078 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_100_upper :
    configurationValueCount 100 53 = 50090 ∧
      configurationIntervalCount 100 969 53 = 1084 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_101_lower :
    configurationValueCount 101 53 = 51100 ∧
      configurationIntervalCount 101 988 53 = 1074 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_101_upper :
    configurationValueCount 101 54 = 51082 ∧
      configurationIntervalCount 101 988 54 = 1084 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_102_lower :
    configurationValueCount 102 53 = 52110 ∧
      configurationIntervalCount 102 1007 53 = 1124 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_102_upper :
    configurationValueCount 102 54 = 52112 ∧
      configurationIntervalCount 102 1007 54 = 1126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_103_lower :
    configurationValueCount 103 54 = 53142 ∧
      configurationIntervalCount 103 1026 54 = 1236 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_103_upper :
    configurationValueCount 103 55 = 53124 ∧
      configurationIntervalCount 103 1026 55 = 1238 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_104_lower :
    configurationValueCount 104 54 = 54172 ∧
      configurationIntervalCount 104 1046 54 = 1078 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_104_upper :
    configurationValueCount 104 55 = 54174 ∧
      configurationIntervalCount 104 1046 55 = 1088 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_105_lower :
    configurationValueCount 105 55 = 55224 ∧
      configurationIntervalCount 105 1065 55 = 1265 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_105_upper :
    configurationValueCount 105 56 = 55206 ∧
      configurationIntervalCount 105 1065 56 = 1287 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_106_lower :
    configurationValueCount 106 56 = 56276 ∧
      configurationIntervalCount 106 1085 56 = 1281 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_106_upper :
    configurationValueCount 106 57 = 56238 ∧
      configurationIntervalCount 106 1085 57 = 1288 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_107_lower :
    configurationValueCount 107 56 = 57346 ∧
      configurationIntervalCount 107 1105 56 = 1291 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_107_upper :
    configurationValueCount 107 57 = 57328 ∧
      configurationIntervalCount 107 1105 57 = 1306 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_108_lower :
    configurationValueCount 108 57 = 58418 ∧
      configurationIntervalCount 108 1125 57 = 1313 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_108_upper :
    configurationValueCount 108 58 = 58380 ∧
      configurationIntervalCount 108 1125 58 = 1331 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_109_lower :
    configurationValueCount 109 57 = 59508 ∧
      configurationIntervalCount 109 1146 57 = 1210 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_109_upper :
    configurationValueCount 109 58 = 59490 ∧
      configurationIntervalCount 109 1146 58 = 1216 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_110_lower :
    configurationValueCount 110 58 = 60600 ∧
      configurationIntervalCount 110 1166 58 = 1335 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_110_upper :
    configurationValueCount 110 59 = 60562 ∧
      configurationIntervalCount 110 1166 59 = 1357 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_111_lower :
    configurationValueCount 111 59 = 61692 ∧
      configurationIntervalCount 111 1187 59 = 1357 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_111_upper :
    configurationValueCount 111 60 = 61634 ∧
      configurationIntervalCount 111 1187 60 = 1367 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_112_lower :
    configurationValueCount 112 59 = 62822 ∧
      configurationIntervalCount 112 1208 59 = 1361 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_112_upper :
    configurationValueCount 112 60 = 62784 ∧
      configurationIntervalCount 112 1208 60 = 1364 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_113_lower :
    configurationValueCount 113 60 = 63934 ∧
      configurationIntervalCount 113 1229 60 = 1383 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_113_upper :
    configurationValueCount 113 61 = 63876 ∧
      configurationIntervalCount 113 1229 61 = 1401 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_114_lower :
    configurationValueCount 114 60 = 65084 ∧
      configurationIntervalCount 114 1251 60 = 1198 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_114_upper :
    configurationValueCount 114 61 = 65046 ∧
      configurationIntervalCount 114 1251 61 = 1208 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_115_lower :
    configurationValueCount 115 61 = 66216 ∧
      configurationIntervalCount 115 1272 61 = 1393 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_115_upper :
    configurationValueCount 115 62 = 66158 ∧
      configurationIntervalCount 115 1272 62 = 1400 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_116_lower :
    configurationValueCount 116 61 = 67386 ∧
      configurationIntervalCount 116 1294 61 = 1296 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_116_upper :
    configurationValueCount 116 62 = 67348 ∧
      configurationIntervalCount 116 1294 62 = 1298 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_117_lower :
    configurationValueCount 117 61 = 68556 ∧
      configurationIntervalCount 117 1316 61 = 1258 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_117_upper :
    configurationValueCount 117 62 = 68538 ∧
      configurationIntervalCount 117 1316 62 = 1264 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_118_lower :
    configurationValueCount 118 62 = 69728 ∧
      configurationIntervalCount 118 1338 62 = 1294 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_118_upper :
    configurationValueCount 118 63 = 69690 ∧
      configurationIntervalCount 118 1338 63 = 1304 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_119_lower :
    configurationValueCount 119 63 = 70900 ∧
      configurationIntervalCount 119 1360 63 = 1398 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_119_upper :
    configurationValueCount 119 64 = 70842 ∧
      configurationIntervalCount 119 1360 64 = 1404 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_120_lower :
    configurationValueCount 120 64 = 72072 ∧
      configurationIntervalCount 120 1382 64 = 1475 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_120_upper :
    configurationValueCount 120 65 = 71994 ∧
      configurationIntervalCount 120 1382 65 = 1497 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_121_lower :
    configurationValueCount 121 64 = 73302 ∧
      configurationIntervalCount 121 1405 64 = 1440 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_121_upper :
    configurationValueCount 121 65 = 73244 ∧
      configurationIntervalCount 121 1405 65 = 1442 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_122_lower :
    configurationValueCount 122 64 = 74532 ∧
      configurationIntervalCount 122 1428 64 = 1370 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_122_upper :
    configurationValueCount 122 65 = 74494 ∧
      configurationIntervalCount 122 1428 65 = 1376 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_123_lower :
    configurationValueCount 123 65 = 75744 ∧
      configurationIntervalCount 123 1451 65 = 1374 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_123_upper :
    configurationValueCount 123 66 = 75686 ∧
      configurationIntervalCount 123 1451 66 = 1384 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_124_lower :
    configurationValueCount 124 66 = 76956 ∧
      configurationIntervalCount 124 1474 66 = 1454 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_124_upper :
    configurationValueCount 124 67 = 76878 ∧
      configurationIntervalCount 124 1474 67 = 1460 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_125_lower :
    configurationValueCount 125 66 = 78226 ∧
      configurationIntervalCount 125 1497 66 = 1527 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_125_upper :
    configurationValueCount 125 67 = 78168 ∧
      configurationIntervalCount 125 1497 67 = 1545 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_126_lower :
    configurationValueCount 126 67 = 79458 ∧
      configurationIntervalCount 126 1521 67 = 1428 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_126_upper :
    configurationValueCount 126 68 = 79380 ∧
      configurationIntervalCount 126 1521 68 = 1434 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_127_lower :
    configurationValueCount 127 67 = 80748 ∧
      configurationIntervalCount 127 1545 67 = 1322 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_127_upper :
    configurationValueCount 127 68 = 80690 ∧
      configurationIntervalCount 127 1545 68 = 1332 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_128_lower :
    configurationValueCount 128 68 = 82000 ∧
      configurationIntervalCount 128 1568 68 = 1571 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_128_upper :
    configurationValueCount 128 69 = 81922 ∧
      configurationIntervalCount 128 1568 69 = 1593 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_129_lower :
    configurationValueCount 129 68 = 83310 ∧
      configurationIntervalCount 129 1593 68 = 1336 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_counts_129_upper :
    configurationValueCount 129 69 = 83252 ∧
      configurationIntervalCount 129 1593 69 = 1342 := by
  decide +kernel

end Quartic.SharpCertificate
