import Quartic.FiniteEndpointInverseMemo26
import Quartic.FiniteEndpointMetadata26Data

/-! Kernel-checked rows of the actual quartic multiplication matrix. -/
namespace Quartic.FiniteEndpointRows26
open FiniteEndpointChecker
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 64000000

certify_sparse_rows certificate from "certificates/finite/n26/sparse.bin" inverse_file "certificates/finite/n26/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse26.binaryInverse row_fn Quartic.FiniteEndpointMetadata26Data.naturalRow nwords 372 start_index 23552 row_count 64

theorem chunk_368 (i : Fin 64) (hi : 23552+i.val < 23751) :
    xorSum ((FiniteEndpointMetadata26Data.naturalRow (23552+i.val)).map
      FiniteEndpointInverse26.binaryInverse) = 2^(23552+i.val) := by
  fin_cases i
  · exact certificate.row_23552
  · exact certificate.row_23553
  · exact certificate.row_23554
  · exact certificate.row_23555
  · exact certificate.row_23556
  · exact certificate.row_23557
  · exact certificate.row_23558
  · exact certificate.row_23559
  · exact certificate.row_23560
  · exact certificate.row_23561
  · exact certificate.row_23562
  · exact certificate.row_23563
  · exact certificate.row_23564
  · exact certificate.row_23565
  · exact certificate.row_23566
  · exact certificate.row_23567
  · exact certificate.row_23568
  · exact certificate.row_23569
  · exact certificate.row_23570
  · exact certificate.row_23571
  · exact certificate.row_23572
  · exact certificate.row_23573
  · exact certificate.row_23574
  · exact certificate.row_23575
  · exact certificate.row_23576
  · exact certificate.row_23577
  · exact certificate.row_23578
  · exact certificate.row_23579
  · exact certificate.row_23580
  · exact certificate.row_23581
  · exact certificate.row_23582
  · exact certificate.row_23583
  · exact certificate.row_23584
  · exact certificate.row_23585
  · exact certificate.row_23586
  · exact certificate.row_23587
  · exact certificate.row_23588
  · exact certificate.row_23589
  · exact certificate.row_23590
  · exact certificate.row_23591
  · exact certificate.row_23592
  · exact certificate.row_23593
  · exact certificate.row_23594
  · exact certificate.row_23595
  · exact certificate.row_23596
  · exact certificate.row_23597
  · exact certificate.row_23598
  · exact certificate.row_23599
  · exact certificate.row_23600
  · exact certificate.row_23601
  · exact certificate.row_23602
  · exact certificate.row_23603
  · exact certificate.row_23604
  · exact certificate.row_23605
  · exact certificate.row_23606
  · exact certificate.row_23607
  · exact certificate.row_23608
  · exact certificate.row_23609
  · exact certificate.row_23610
  · exact certificate.row_23611
  · exact certificate.row_23612
  · exact certificate.row_23613
  · exact certificate.row_23614
  · exact certificate.row_23615

certify_sparse_rows certificate from "certificates/finite/n26/sparse.bin" inverse_file "certificates/finite/n26/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse26.binaryInverse row_fn Quartic.FiniteEndpointMetadata26Data.naturalRow nwords 372 start_index 23616 row_count 64

theorem chunk_369 (i : Fin 64) (hi : 23616+i.val < 23751) :
    xorSum ((FiniteEndpointMetadata26Data.naturalRow (23616+i.val)).map
      FiniteEndpointInverse26.binaryInverse) = 2^(23616+i.val) := by
  fin_cases i
  · exact certificate.row_23616
  · exact certificate.row_23617
  · exact certificate.row_23618
  · exact certificate.row_23619
  · exact certificate.row_23620
  · exact certificate.row_23621
  · exact certificate.row_23622
  · exact certificate.row_23623
  · exact certificate.row_23624
  · exact certificate.row_23625
  · exact certificate.row_23626
  · exact certificate.row_23627
  · exact certificate.row_23628
  · exact certificate.row_23629
  · exact certificate.row_23630
  · exact certificate.row_23631
  · exact certificate.row_23632
  · exact certificate.row_23633
  · exact certificate.row_23634
  · exact certificate.row_23635
  · exact certificate.row_23636
  · exact certificate.row_23637
  · exact certificate.row_23638
  · exact certificate.row_23639
  · exact certificate.row_23640
  · exact certificate.row_23641
  · exact certificate.row_23642
  · exact certificate.row_23643
  · exact certificate.row_23644
  · exact certificate.row_23645
  · exact certificate.row_23646
  · exact certificate.row_23647
  · exact certificate.row_23648
  · exact certificate.row_23649
  · exact certificate.row_23650
  · exact certificate.row_23651
  · exact certificate.row_23652
  · exact certificate.row_23653
  · exact certificate.row_23654
  · exact certificate.row_23655
  · exact certificate.row_23656
  · exact certificate.row_23657
  · exact certificate.row_23658
  · exact certificate.row_23659
  · exact certificate.row_23660
  · exact certificate.row_23661
  · exact certificate.row_23662
  · exact certificate.row_23663
  · exact certificate.row_23664
  · exact certificate.row_23665
  · exact certificate.row_23666
  · exact certificate.row_23667
  · exact certificate.row_23668
  · exact certificate.row_23669
  · exact certificate.row_23670
  · exact certificate.row_23671
  · exact certificate.row_23672
  · exact certificate.row_23673
  · exact certificate.row_23674
  · exact certificate.row_23675
  · exact certificate.row_23676
  · exact certificate.row_23677
  · exact certificate.row_23678
  · exact certificate.row_23679

certify_sparse_rows certificate from "certificates/finite/n26/sparse.bin" inverse_file "certificates/finite/n26/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse26.binaryInverse row_fn Quartic.FiniteEndpointMetadata26Data.naturalRow nwords 372 start_index 23680 row_count 64

theorem chunk_370 (i : Fin 64) (hi : 23680+i.val < 23751) :
    xorSum ((FiniteEndpointMetadata26Data.naturalRow (23680+i.val)).map
      FiniteEndpointInverse26.binaryInverse) = 2^(23680+i.val) := by
  fin_cases i
  · exact certificate.row_23680
  · exact certificate.row_23681
  · exact certificate.row_23682
  · exact certificate.row_23683
  · exact certificate.row_23684
  · exact certificate.row_23685
  · exact certificate.row_23686
  · exact certificate.row_23687
  · exact certificate.row_23688
  · exact certificate.row_23689
  · exact certificate.row_23690
  · exact certificate.row_23691
  · exact certificate.row_23692
  · exact certificate.row_23693
  · exact certificate.row_23694
  · exact certificate.row_23695
  · exact certificate.row_23696
  · exact certificate.row_23697
  · exact certificate.row_23698
  · exact certificate.row_23699
  · exact certificate.row_23700
  · exact certificate.row_23701
  · exact certificate.row_23702
  · exact certificate.row_23703
  · exact certificate.row_23704
  · exact certificate.row_23705
  · exact certificate.row_23706
  · exact certificate.row_23707
  · exact certificate.row_23708
  · exact certificate.row_23709
  · exact certificate.row_23710
  · exact certificate.row_23711
  · exact certificate.row_23712
  · exact certificate.row_23713
  · exact certificate.row_23714
  · exact certificate.row_23715
  · exact certificate.row_23716
  · exact certificate.row_23717
  · exact certificate.row_23718
  · exact certificate.row_23719
  · exact certificate.row_23720
  · exact certificate.row_23721
  · exact certificate.row_23722
  · exact certificate.row_23723
  · exact certificate.row_23724
  · exact certificate.row_23725
  · exact certificate.row_23726
  · exact certificate.row_23727
  · exact certificate.row_23728
  · exact certificate.row_23729
  · exact certificate.row_23730
  · exact certificate.row_23731
  · exact certificate.row_23732
  · exact certificate.row_23733
  · exact certificate.row_23734
  · exact certificate.row_23735
  · exact certificate.row_23736
  · exact certificate.row_23737
  · exact certificate.row_23738
  · exact certificate.row_23739
  · exact certificate.row_23740
  · exact certificate.row_23741
  · exact certificate.row_23742
  · exact certificate.row_23743

certify_sparse_rows certificate from "certificates/finite/n26/sparse.bin" inverse_file "certificates/finite/n26/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse26.binaryInverse row_fn Quartic.FiniteEndpointMetadata26Data.naturalRow nwords 372 start_index 23744 row_count 7

theorem chunk_371 (i : Fin 64) (hi : 23744+i.val < 23751) :
    xorSum ((FiniteEndpointMetadata26Data.naturalRow (23744+i.val)).map
      FiniteEndpointInverse26.binaryInverse) = 2^(23744+i.val) := by
  fin_cases i
  · exact certificate.row_23744
  · exact certificate.row_23745
  · exact certificate.row_23746
  · exact certificate.row_23747
  · exact certificate.row_23748
  · exact certificate.row_23749
  · exact certificate.row_23750
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi

end Quartic.FiniteEndpointRows26
