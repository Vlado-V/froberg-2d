import Quartic.FiniteEndpointInverseMemo23
import Quartic.FiniteEndpointMetadata23Data

/-! Kernel-checked rows of the actual quartic multiplication matrix. -/
namespace Quartic.FiniteEndpointRows23
open FiniteEndpointChecker
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 64000000

certify_sparse_rows certificate from "certificates/finite/n23/sparse.bin" inverse_file "certificates/finite/n23/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse23.binaryInverse row_fn Quartic.FiniteEndpointMetadata23Data.naturalRow nwords 234 start_index 14336 row_count 64

theorem chunk_224 (i : Fin 64) (hi : 14336+i.val < 14950) :
    xorSum ((FiniteEndpointMetadata23Data.naturalRow (14336+i.val)).map
      FiniteEndpointInverse23.binaryInverse) = 2^(14336+i.val) := by
  fin_cases i
  · exact certificate.row_14336
  · exact certificate.row_14337
  · exact certificate.row_14338
  · exact certificate.row_14339
  · exact certificate.row_14340
  · exact certificate.row_14341
  · exact certificate.row_14342
  · exact certificate.row_14343
  · exact certificate.row_14344
  · exact certificate.row_14345
  · exact certificate.row_14346
  · exact certificate.row_14347
  · exact certificate.row_14348
  · exact certificate.row_14349
  · exact certificate.row_14350
  · exact certificate.row_14351
  · exact certificate.row_14352
  · exact certificate.row_14353
  · exact certificate.row_14354
  · exact certificate.row_14355
  · exact certificate.row_14356
  · exact certificate.row_14357
  · exact certificate.row_14358
  · exact certificate.row_14359
  · exact certificate.row_14360
  · exact certificate.row_14361
  · exact certificate.row_14362
  · exact certificate.row_14363
  · exact certificate.row_14364
  · exact certificate.row_14365
  · exact certificate.row_14366
  · exact certificate.row_14367
  · exact certificate.row_14368
  · exact certificate.row_14369
  · exact certificate.row_14370
  · exact certificate.row_14371
  · exact certificate.row_14372
  · exact certificate.row_14373
  · exact certificate.row_14374
  · exact certificate.row_14375
  · exact certificate.row_14376
  · exact certificate.row_14377
  · exact certificate.row_14378
  · exact certificate.row_14379
  · exact certificate.row_14380
  · exact certificate.row_14381
  · exact certificate.row_14382
  · exact certificate.row_14383
  · exact certificate.row_14384
  · exact certificate.row_14385
  · exact certificate.row_14386
  · exact certificate.row_14387
  · exact certificate.row_14388
  · exact certificate.row_14389
  · exact certificate.row_14390
  · exact certificate.row_14391
  · exact certificate.row_14392
  · exact certificate.row_14393
  · exact certificate.row_14394
  · exact certificate.row_14395
  · exact certificate.row_14396
  · exact certificate.row_14397
  · exact certificate.row_14398
  · exact certificate.row_14399

certify_sparse_rows certificate from "certificates/finite/n23/sparse.bin" inverse_file "certificates/finite/n23/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse23.binaryInverse row_fn Quartic.FiniteEndpointMetadata23Data.naturalRow nwords 234 start_index 14400 row_count 64

theorem chunk_225 (i : Fin 64) (hi : 14400+i.val < 14950) :
    xorSum ((FiniteEndpointMetadata23Data.naturalRow (14400+i.val)).map
      FiniteEndpointInverse23.binaryInverse) = 2^(14400+i.val) := by
  fin_cases i
  · exact certificate.row_14400
  · exact certificate.row_14401
  · exact certificate.row_14402
  · exact certificate.row_14403
  · exact certificate.row_14404
  · exact certificate.row_14405
  · exact certificate.row_14406
  · exact certificate.row_14407
  · exact certificate.row_14408
  · exact certificate.row_14409
  · exact certificate.row_14410
  · exact certificate.row_14411
  · exact certificate.row_14412
  · exact certificate.row_14413
  · exact certificate.row_14414
  · exact certificate.row_14415
  · exact certificate.row_14416
  · exact certificate.row_14417
  · exact certificate.row_14418
  · exact certificate.row_14419
  · exact certificate.row_14420
  · exact certificate.row_14421
  · exact certificate.row_14422
  · exact certificate.row_14423
  · exact certificate.row_14424
  · exact certificate.row_14425
  · exact certificate.row_14426
  · exact certificate.row_14427
  · exact certificate.row_14428
  · exact certificate.row_14429
  · exact certificate.row_14430
  · exact certificate.row_14431
  · exact certificate.row_14432
  · exact certificate.row_14433
  · exact certificate.row_14434
  · exact certificate.row_14435
  · exact certificate.row_14436
  · exact certificate.row_14437
  · exact certificate.row_14438
  · exact certificate.row_14439
  · exact certificate.row_14440
  · exact certificate.row_14441
  · exact certificate.row_14442
  · exact certificate.row_14443
  · exact certificate.row_14444
  · exact certificate.row_14445
  · exact certificate.row_14446
  · exact certificate.row_14447
  · exact certificate.row_14448
  · exact certificate.row_14449
  · exact certificate.row_14450
  · exact certificate.row_14451
  · exact certificate.row_14452
  · exact certificate.row_14453
  · exact certificate.row_14454
  · exact certificate.row_14455
  · exact certificate.row_14456
  · exact certificate.row_14457
  · exact certificate.row_14458
  · exact certificate.row_14459
  · exact certificate.row_14460
  · exact certificate.row_14461
  · exact certificate.row_14462
  · exact certificate.row_14463

certify_sparse_rows certificate from "certificates/finite/n23/sparse.bin" inverse_file "certificates/finite/n23/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse23.binaryInverse row_fn Quartic.FiniteEndpointMetadata23Data.naturalRow nwords 234 start_index 14464 row_count 64

theorem chunk_226 (i : Fin 64) (hi : 14464+i.val < 14950) :
    xorSum ((FiniteEndpointMetadata23Data.naturalRow (14464+i.val)).map
      FiniteEndpointInverse23.binaryInverse) = 2^(14464+i.val) := by
  fin_cases i
  · exact certificate.row_14464
  · exact certificate.row_14465
  · exact certificate.row_14466
  · exact certificate.row_14467
  · exact certificate.row_14468
  · exact certificate.row_14469
  · exact certificate.row_14470
  · exact certificate.row_14471
  · exact certificate.row_14472
  · exact certificate.row_14473
  · exact certificate.row_14474
  · exact certificate.row_14475
  · exact certificate.row_14476
  · exact certificate.row_14477
  · exact certificate.row_14478
  · exact certificate.row_14479
  · exact certificate.row_14480
  · exact certificate.row_14481
  · exact certificate.row_14482
  · exact certificate.row_14483
  · exact certificate.row_14484
  · exact certificate.row_14485
  · exact certificate.row_14486
  · exact certificate.row_14487
  · exact certificate.row_14488
  · exact certificate.row_14489
  · exact certificate.row_14490
  · exact certificate.row_14491
  · exact certificate.row_14492
  · exact certificate.row_14493
  · exact certificate.row_14494
  · exact certificate.row_14495
  · exact certificate.row_14496
  · exact certificate.row_14497
  · exact certificate.row_14498
  · exact certificate.row_14499
  · exact certificate.row_14500
  · exact certificate.row_14501
  · exact certificate.row_14502
  · exact certificate.row_14503
  · exact certificate.row_14504
  · exact certificate.row_14505
  · exact certificate.row_14506
  · exact certificate.row_14507
  · exact certificate.row_14508
  · exact certificate.row_14509
  · exact certificate.row_14510
  · exact certificate.row_14511
  · exact certificate.row_14512
  · exact certificate.row_14513
  · exact certificate.row_14514
  · exact certificate.row_14515
  · exact certificate.row_14516
  · exact certificate.row_14517
  · exact certificate.row_14518
  · exact certificate.row_14519
  · exact certificate.row_14520
  · exact certificate.row_14521
  · exact certificate.row_14522
  · exact certificate.row_14523
  · exact certificate.row_14524
  · exact certificate.row_14525
  · exact certificate.row_14526
  · exact certificate.row_14527

certify_sparse_rows certificate from "certificates/finite/n23/sparse.bin" inverse_file "certificates/finite/n23/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse23.binaryInverse row_fn Quartic.FiniteEndpointMetadata23Data.naturalRow nwords 234 start_index 14528 row_count 64

theorem chunk_227 (i : Fin 64) (hi : 14528+i.val < 14950) :
    xorSum ((FiniteEndpointMetadata23Data.naturalRow (14528+i.val)).map
      FiniteEndpointInverse23.binaryInverse) = 2^(14528+i.val) := by
  fin_cases i
  · exact certificate.row_14528
  · exact certificate.row_14529
  · exact certificate.row_14530
  · exact certificate.row_14531
  · exact certificate.row_14532
  · exact certificate.row_14533
  · exact certificate.row_14534
  · exact certificate.row_14535
  · exact certificate.row_14536
  · exact certificate.row_14537
  · exact certificate.row_14538
  · exact certificate.row_14539
  · exact certificate.row_14540
  · exact certificate.row_14541
  · exact certificate.row_14542
  · exact certificate.row_14543
  · exact certificate.row_14544
  · exact certificate.row_14545
  · exact certificate.row_14546
  · exact certificate.row_14547
  · exact certificate.row_14548
  · exact certificate.row_14549
  · exact certificate.row_14550
  · exact certificate.row_14551
  · exact certificate.row_14552
  · exact certificate.row_14553
  · exact certificate.row_14554
  · exact certificate.row_14555
  · exact certificate.row_14556
  · exact certificate.row_14557
  · exact certificate.row_14558
  · exact certificate.row_14559
  · exact certificate.row_14560
  · exact certificate.row_14561
  · exact certificate.row_14562
  · exact certificate.row_14563
  · exact certificate.row_14564
  · exact certificate.row_14565
  · exact certificate.row_14566
  · exact certificate.row_14567
  · exact certificate.row_14568
  · exact certificate.row_14569
  · exact certificate.row_14570
  · exact certificate.row_14571
  · exact certificate.row_14572
  · exact certificate.row_14573
  · exact certificate.row_14574
  · exact certificate.row_14575
  · exact certificate.row_14576
  · exact certificate.row_14577
  · exact certificate.row_14578
  · exact certificate.row_14579
  · exact certificate.row_14580
  · exact certificate.row_14581
  · exact certificate.row_14582
  · exact certificate.row_14583
  · exact certificate.row_14584
  · exact certificate.row_14585
  · exact certificate.row_14586
  · exact certificate.row_14587
  · exact certificate.row_14588
  · exact certificate.row_14589
  · exact certificate.row_14590
  · exact certificate.row_14591

certify_sparse_rows certificate from "certificates/finite/n23/sparse.bin" inverse_file "certificates/finite/n23/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse23.binaryInverse row_fn Quartic.FiniteEndpointMetadata23Data.naturalRow nwords 234 start_index 14592 row_count 64

theorem chunk_228 (i : Fin 64) (hi : 14592+i.val < 14950) :
    xorSum ((FiniteEndpointMetadata23Data.naturalRow (14592+i.val)).map
      FiniteEndpointInverse23.binaryInverse) = 2^(14592+i.val) := by
  fin_cases i
  · exact certificate.row_14592
  · exact certificate.row_14593
  · exact certificate.row_14594
  · exact certificate.row_14595
  · exact certificate.row_14596
  · exact certificate.row_14597
  · exact certificate.row_14598
  · exact certificate.row_14599
  · exact certificate.row_14600
  · exact certificate.row_14601
  · exact certificate.row_14602
  · exact certificate.row_14603
  · exact certificate.row_14604
  · exact certificate.row_14605
  · exact certificate.row_14606
  · exact certificate.row_14607
  · exact certificate.row_14608
  · exact certificate.row_14609
  · exact certificate.row_14610
  · exact certificate.row_14611
  · exact certificate.row_14612
  · exact certificate.row_14613
  · exact certificate.row_14614
  · exact certificate.row_14615
  · exact certificate.row_14616
  · exact certificate.row_14617
  · exact certificate.row_14618
  · exact certificate.row_14619
  · exact certificate.row_14620
  · exact certificate.row_14621
  · exact certificate.row_14622
  · exact certificate.row_14623
  · exact certificate.row_14624
  · exact certificate.row_14625
  · exact certificate.row_14626
  · exact certificate.row_14627
  · exact certificate.row_14628
  · exact certificate.row_14629
  · exact certificate.row_14630
  · exact certificate.row_14631
  · exact certificate.row_14632
  · exact certificate.row_14633
  · exact certificate.row_14634
  · exact certificate.row_14635
  · exact certificate.row_14636
  · exact certificate.row_14637
  · exact certificate.row_14638
  · exact certificate.row_14639
  · exact certificate.row_14640
  · exact certificate.row_14641
  · exact certificate.row_14642
  · exact certificate.row_14643
  · exact certificate.row_14644
  · exact certificate.row_14645
  · exact certificate.row_14646
  · exact certificate.row_14647
  · exact certificate.row_14648
  · exact certificate.row_14649
  · exact certificate.row_14650
  · exact certificate.row_14651
  · exact certificate.row_14652
  · exact certificate.row_14653
  · exact certificate.row_14654
  · exact certificate.row_14655

certify_sparse_rows certificate from "certificates/finite/n23/sparse.bin" inverse_file "certificates/finite/n23/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse23.binaryInverse row_fn Quartic.FiniteEndpointMetadata23Data.naturalRow nwords 234 start_index 14656 row_count 64

theorem chunk_229 (i : Fin 64) (hi : 14656+i.val < 14950) :
    xorSum ((FiniteEndpointMetadata23Data.naturalRow (14656+i.val)).map
      FiniteEndpointInverse23.binaryInverse) = 2^(14656+i.val) := by
  fin_cases i
  · exact certificate.row_14656
  · exact certificate.row_14657
  · exact certificate.row_14658
  · exact certificate.row_14659
  · exact certificate.row_14660
  · exact certificate.row_14661
  · exact certificate.row_14662
  · exact certificate.row_14663
  · exact certificate.row_14664
  · exact certificate.row_14665
  · exact certificate.row_14666
  · exact certificate.row_14667
  · exact certificate.row_14668
  · exact certificate.row_14669
  · exact certificate.row_14670
  · exact certificate.row_14671
  · exact certificate.row_14672
  · exact certificate.row_14673
  · exact certificate.row_14674
  · exact certificate.row_14675
  · exact certificate.row_14676
  · exact certificate.row_14677
  · exact certificate.row_14678
  · exact certificate.row_14679
  · exact certificate.row_14680
  · exact certificate.row_14681
  · exact certificate.row_14682
  · exact certificate.row_14683
  · exact certificate.row_14684
  · exact certificate.row_14685
  · exact certificate.row_14686
  · exact certificate.row_14687
  · exact certificate.row_14688
  · exact certificate.row_14689
  · exact certificate.row_14690
  · exact certificate.row_14691
  · exact certificate.row_14692
  · exact certificate.row_14693
  · exact certificate.row_14694
  · exact certificate.row_14695
  · exact certificate.row_14696
  · exact certificate.row_14697
  · exact certificate.row_14698
  · exact certificate.row_14699
  · exact certificate.row_14700
  · exact certificate.row_14701
  · exact certificate.row_14702
  · exact certificate.row_14703
  · exact certificate.row_14704
  · exact certificate.row_14705
  · exact certificate.row_14706
  · exact certificate.row_14707
  · exact certificate.row_14708
  · exact certificate.row_14709
  · exact certificate.row_14710
  · exact certificate.row_14711
  · exact certificate.row_14712
  · exact certificate.row_14713
  · exact certificate.row_14714
  · exact certificate.row_14715
  · exact certificate.row_14716
  · exact certificate.row_14717
  · exact certificate.row_14718
  · exact certificate.row_14719

certify_sparse_rows certificate from "certificates/finite/n23/sparse.bin" inverse_file "certificates/finite/n23/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse23.binaryInverse row_fn Quartic.FiniteEndpointMetadata23Data.naturalRow nwords 234 start_index 14720 row_count 64

theorem chunk_230 (i : Fin 64) (hi : 14720+i.val < 14950) :
    xorSum ((FiniteEndpointMetadata23Data.naturalRow (14720+i.val)).map
      FiniteEndpointInverse23.binaryInverse) = 2^(14720+i.val) := by
  fin_cases i
  · exact certificate.row_14720
  · exact certificate.row_14721
  · exact certificate.row_14722
  · exact certificate.row_14723
  · exact certificate.row_14724
  · exact certificate.row_14725
  · exact certificate.row_14726
  · exact certificate.row_14727
  · exact certificate.row_14728
  · exact certificate.row_14729
  · exact certificate.row_14730
  · exact certificate.row_14731
  · exact certificate.row_14732
  · exact certificate.row_14733
  · exact certificate.row_14734
  · exact certificate.row_14735
  · exact certificate.row_14736
  · exact certificate.row_14737
  · exact certificate.row_14738
  · exact certificate.row_14739
  · exact certificate.row_14740
  · exact certificate.row_14741
  · exact certificate.row_14742
  · exact certificate.row_14743
  · exact certificate.row_14744
  · exact certificate.row_14745
  · exact certificate.row_14746
  · exact certificate.row_14747
  · exact certificate.row_14748
  · exact certificate.row_14749
  · exact certificate.row_14750
  · exact certificate.row_14751
  · exact certificate.row_14752
  · exact certificate.row_14753
  · exact certificate.row_14754
  · exact certificate.row_14755
  · exact certificate.row_14756
  · exact certificate.row_14757
  · exact certificate.row_14758
  · exact certificate.row_14759
  · exact certificate.row_14760
  · exact certificate.row_14761
  · exact certificate.row_14762
  · exact certificate.row_14763
  · exact certificate.row_14764
  · exact certificate.row_14765
  · exact certificate.row_14766
  · exact certificate.row_14767
  · exact certificate.row_14768
  · exact certificate.row_14769
  · exact certificate.row_14770
  · exact certificate.row_14771
  · exact certificate.row_14772
  · exact certificate.row_14773
  · exact certificate.row_14774
  · exact certificate.row_14775
  · exact certificate.row_14776
  · exact certificate.row_14777
  · exact certificate.row_14778
  · exact certificate.row_14779
  · exact certificate.row_14780
  · exact certificate.row_14781
  · exact certificate.row_14782
  · exact certificate.row_14783

certify_sparse_rows certificate from "certificates/finite/n23/sparse.bin" inverse_file "certificates/finite/n23/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse23.binaryInverse row_fn Quartic.FiniteEndpointMetadata23Data.naturalRow nwords 234 start_index 14784 row_count 64

theorem chunk_231 (i : Fin 64) (hi : 14784+i.val < 14950) :
    xorSum ((FiniteEndpointMetadata23Data.naturalRow (14784+i.val)).map
      FiniteEndpointInverse23.binaryInverse) = 2^(14784+i.val) := by
  fin_cases i
  · exact certificate.row_14784
  · exact certificate.row_14785
  · exact certificate.row_14786
  · exact certificate.row_14787
  · exact certificate.row_14788
  · exact certificate.row_14789
  · exact certificate.row_14790
  · exact certificate.row_14791
  · exact certificate.row_14792
  · exact certificate.row_14793
  · exact certificate.row_14794
  · exact certificate.row_14795
  · exact certificate.row_14796
  · exact certificate.row_14797
  · exact certificate.row_14798
  · exact certificate.row_14799
  · exact certificate.row_14800
  · exact certificate.row_14801
  · exact certificate.row_14802
  · exact certificate.row_14803
  · exact certificate.row_14804
  · exact certificate.row_14805
  · exact certificate.row_14806
  · exact certificate.row_14807
  · exact certificate.row_14808
  · exact certificate.row_14809
  · exact certificate.row_14810
  · exact certificate.row_14811
  · exact certificate.row_14812
  · exact certificate.row_14813
  · exact certificate.row_14814
  · exact certificate.row_14815
  · exact certificate.row_14816
  · exact certificate.row_14817
  · exact certificate.row_14818
  · exact certificate.row_14819
  · exact certificate.row_14820
  · exact certificate.row_14821
  · exact certificate.row_14822
  · exact certificate.row_14823
  · exact certificate.row_14824
  · exact certificate.row_14825
  · exact certificate.row_14826
  · exact certificate.row_14827
  · exact certificate.row_14828
  · exact certificate.row_14829
  · exact certificate.row_14830
  · exact certificate.row_14831
  · exact certificate.row_14832
  · exact certificate.row_14833
  · exact certificate.row_14834
  · exact certificate.row_14835
  · exact certificate.row_14836
  · exact certificate.row_14837
  · exact certificate.row_14838
  · exact certificate.row_14839
  · exact certificate.row_14840
  · exact certificate.row_14841
  · exact certificate.row_14842
  · exact certificate.row_14843
  · exact certificate.row_14844
  · exact certificate.row_14845
  · exact certificate.row_14846
  · exact certificate.row_14847

certify_sparse_rows certificate from "certificates/finite/n23/sparse.bin" inverse_file "certificates/finite/n23/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse23.binaryInverse row_fn Quartic.FiniteEndpointMetadata23Data.naturalRow nwords 234 start_index 14848 row_count 64

theorem chunk_232 (i : Fin 64) (hi : 14848+i.val < 14950) :
    xorSum ((FiniteEndpointMetadata23Data.naturalRow (14848+i.val)).map
      FiniteEndpointInverse23.binaryInverse) = 2^(14848+i.val) := by
  fin_cases i
  · exact certificate.row_14848
  · exact certificate.row_14849
  · exact certificate.row_14850
  · exact certificate.row_14851
  · exact certificate.row_14852
  · exact certificate.row_14853
  · exact certificate.row_14854
  · exact certificate.row_14855
  · exact certificate.row_14856
  · exact certificate.row_14857
  · exact certificate.row_14858
  · exact certificate.row_14859
  · exact certificate.row_14860
  · exact certificate.row_14861
  · exact certificate.row_14862
  · exact certificate.row_14863
  · exact certificate.row_14864
  · exact certificate.row_14865
  · exact certificate.row_14866
  · exact certificate.row_14867
  · exact certificate.row_14868
  · exact certificate.row_14869
  · exact certificate.row_14870
  · exact certificate.row_14871
  · exact certificate.row_14872
  · exact certificate.row_14873
  · exact certificate.row_14874
  · exact certificate.row_14875
  · exact certificate.row_14876
  · exact certificate.row_14877
  · exact certificate.row_14878
  · exact certificate.row_14879
  · exact certificate.row_14880
  · exact certificate.row_14881
  · exact certificate.row_14882
  · exact certificate.row_14883
  · exact certificate.row_14884
  · exact certificate.row_14885
  · exact certificate.row_14886
  · exact certificate.row_14887
  · exact certificate.row_14888
  · exact certificate.row_14889
  · exact certificate.row_14890
  · exact certificate.row_14891
  · exact certificate.row_14892
  · exact certificate.row_14893
  · exact certificate.row_14894
  · exact certificate.row_14895
  · exact certificate.row_14896
  · exact certificate.row_14897
  · exact certificate.row_14898
  · exact certificate.row_14899
  · exact certificate.row_14900
  · exact certificate.row_14901
  · exact certificate.row_14902
  · exact certificate.row_14903
  · exact certificate.row_14904
  · exact certificate.row_14905
  · exact certificate.row_14906
  · exact certificate.row_14907
  · exact certificate.row_14908
  · exact certificate.row_14909
  · exact certificate.row_14910
  · exact certificate.row_14911

certify_sparse_rows certificate from "certificates/finite/n23/sparse.bin" inverse_file "certificates/finite/n23/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse23.binaryInverse row_fn Quartic.FiniteEndpointMetadata23Data.naturalRow nwords 234 start_index 14912 row_count 38

theorem chunk_233 (i : Fin 64) (hi : 14912+i.val < 14950) :
    xorSum ((FiniteEndpointMetadata23Data.naturalRow (14912+i.val)).map
      FiniteEndpointInverse23.binaryInverse) = 2^(14912+i.val) := by
  fin_cases i
  · exact certificate.row_14912
  · exact certificate.row_14913
  · exact certificate.row_14914
  · exact certificate.row_14915
  · exact certificate.row_14916
  · exact certificate.row_14917
  · exact certificate.row_14918
  · exact certificate.row_14919
  · exact certificate.row_14920
  · exact certificate.row_14921
  · exact certificate.row_14922
  · exact certificate.row_14923
  · exact certificate.row_14924
  · exact certificate.row_14925
  · exact certificate.row_14926
  · exact certificate.row_14927
  · exact certificate.row_14928
  · exact certificate.row_14929
  · exact certificate.row_14930
  · exact certificate.row_14931
  · exact certificate.row_14932
  · exact certificate.row_14933
  · exact certificate.row_14934
  · exact certificate.row_14935
  · exact certificate.row_14936
  · exact certificate.row_14937
  · exact certificate.row_14938
  · exact certificate.row_14939
  · exact certificate.row_14940
  · exact certificate.row_14941
  · exact certificate.row_14942
  · exact certificate.row_14943
  · exact certificate.row_14944
  · exact certificate.row_14945
  · exact certificate.row_14946
  · exact certificate.row_14947
  · exact certificate.row_14948
  · exact certificate.row_14949
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

end Quartic.FiniteEndpointRows23
