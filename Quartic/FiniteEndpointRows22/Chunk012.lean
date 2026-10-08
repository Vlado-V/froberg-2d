import Quartic.FiniteEndpointInverseMemo22
import Quartic.FiniteEndpointMetadata22Data

/-! Kernel-checked rows of the actual quartic multiplication matrix. -/
namespace Quartic.FiniteEndpointRows22
open FiniteEndpointChecker
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 64000000

certify_sparse_rows certificate from "certificates/finite/n22/sparse.bin" inverse_file "certificates/finite/n22/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse22.binaryInverse row_fn Quartic.FiniteEndpointMetadata22Data.naturalRow nwords 198 start_index 12288 row_count 64

theorem chunk_192 (i : Fin 64) (hi : 12288+i.val < 12650) :
    xorSum ((FiniteEndpointMetadata22Data.naturalRow (12288+i.val)).map
      FiniteEndpointInverse22.binaryInverse) = 2^(12288+i.val) := by
  fin_cases i
  · exact certificate.row_12288
  · exact certificate.row_12289
  · exact certificate.row_12290
  · exact certificate.row_12291
  · exact certificate.row_12292
  · exact certificate.row_12293
  · exact certificate.row_12294
  · exact certificate.row_12295
  · exact certificate.row_12296
  · exact certificate.row_12297
  · exact certificate.row_12298
  · exact certificate.row_12299
  · exact certificate.row_12300
  · exact certificate.row_12301
  · exact certificate.row_12302
  · exact certificate.row_12303
  · exact certificate.row_12304
  · exact certificate.row_12305
  · exact certificate.row_12306
  · exact certificate.row_12307
  · exact certificate.row_12308
  · exact certificate.row_12309
  · exact certificate.row_12310
  · exact certificate.row_12311
  · exact certificate.row_12312
  · exact certificate.row_12313
  · exact certificate.row_12314
  · exact certificate.row_12315
  · exact certificate.row_12316
  · exact certificate.row_12317
  · exact certificate.row_12318
  · exact certificate.row_12319
  · exact certificate.row_12320
  · exact certificate.row_12321
  · exact certificate.row_12322
  · exact certificate.row_12323
  · exact certificate.row_12324
  · exact certificate.row_12325
  · exact certificate.row_12326
  · exact certificate.row_12327
  · exact certificate.row_12328
  · exact certificate.row_12329
  · exact certificate.row_12330
  · exact certificate.row_12331
  · exact certificate.row_12332
  · exact certificate.row_12333
  · exact certificate.row_12334
  · exact certificate.row_12335
  · exact certificate.row_12336
  · exact certificate.row_12337
  · exact certificate.row_12338
  · exact certificate.row_12339
  · exact certificate.row_12340
  · exact certificate.row_12341
  · exact certificate.row_12342
  · exact certificate.row_12343
  · exact certificate.row_12344
  · exact certificate.row_12345
  · exact certificate.row_12346
  · exact certificate.row_12347
  · exact certificate.row_12348
  · exact certificate.row_12349
  · exact certificate.row_12350
  · exact certificate.row_12351

certify_sparse_rows certificate from "certificates/finite/n22/sparse.bin" inverse_file "certificates/finite/n22/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse22.binaryInverse row_fn Quartic.FiniteEndpointMetadata22Data.naturalRow nwords 198 start_index 12352 row_count 64

theorem chunk_193 (i : Fin 64) (hi : 12352+i.val < 12650) :
    xorSum ((FiniteEndpointMetadata22Data.naturalRow (12352+i.val)).map
      FiniteEndpointInverse22.binaryInverse) = 2^(12352+i.val) := by
  fin_cases i
  · exact certificate.row_12352
  · exact certificate.row_12353
  · exact certificate.row_12354
  · exact certificate.row_12355
  · exact certificate.row_12356
  · exact certificate.row_12357
  · exact certificate.row_12358
  · exact certificate.row_12359
  · exact certificate.row_12360
  · exact certificate.row_12361
  · exact certificate.row_12362
  · exact certificate.row_12363
  · exact certificate.row_12364
  · exact certificate.row_12365
  · exact certificate.row_12366
  · exact certificate.row_12367
  · exact certificate.row_12368
  · exact certificate.row_12369
  · exact certificate.row_12370
  · exact certificate.row_12371
  · exact certificate.row_12372
  · exact certificate.row_12373
  · exact certificate.row_12374
  · exact certificate.row_12375
  · exact certificate.row_12376
  · exact certificate.row_12377
  · exact certificate.row_12378
  · exact certificate.row_12379
  · exact certificate.row_12380
  · exact certificate.row_12381
  · exact certificate.row_12382
  · exact certificate.row_12383
  · exact certificate.row_12384
  · exact certificate.row_12385
  · exact certificate.row_12386
  · exact certificate.row_12387
  · exact certificate.row_12388
  · exact certificate.row_12389
  · exact certificate.row_12390
  · exact certificate.row_12391
  · exact certificate.row_12392
  · exact certificate.row_12393
  · exact certificate.row_12394
  · exact certificate.row_12395
  · exact certificate.row_12396
  · exact certificate.row_12397
  · exact certificate.row_12398
  · exact certificate.row_12399
  · exact certificate.row_12400
  · exact certificate.row_12401
  · exact certificate.row_12402
  · exact certificate.row_12403
  · exact certificate.row_12404
  · exact certificate.row_12405
  · exact certificate.row_12406
  · exact certificate.row_12407
  · exact certificate.row_12408
  · exact certificate.row_12409
  · exact certificate.row_12410
  · exact certificate.row_12411
  · exact certificate.row_12412
  · exact certificate.row_12413
  · exact certificate.row_12414
  · exact certificate.row_12415

certify_sparse_rows certificate from "certificates/finite/n22/sparse.bin" inverse_file "certificates/finite/n22/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse22.binaryInverse row_fn Quartic.FiniteEndpointMetadata22Data.naturalRow nwords 198 start_index 12416 row_count 64

theorem chunk_194 (i : Fin 64) (hi : 12416+i.val < 12650) :
    xorSum ((FiniteEndpointMetadata22Data.naturalRow (12416+i.val)).map
      FiniteEndpointInverse22.binaryInverse) = 2^(12416+i.val) := by
  fin_cases i
  · exact certificate.row_12416
  · exact certificate.row_12417
  · exact certificate.row_12418
  · exact certificate.row_12419
  · exact certificate.row_12420
  · exact certificate.row_12421
  · exact certificate.row_12422
  · exact certificate.row_12423
  · exact certificate.row_12424
  · exact certificate.row_12425
  · exact certificate.row_12426
  · exact certificate.row_12427
  · exact certificate.row_12428
  · exact certificate.row_12429
  · exact certificate.row_12430
  · exact certificate.row_12431
  · exact certificate.row_12432
  · exact certificate.row_12433
  · exact certificate.row_12434
  · exact certificate.row_12435
  · exact certificate.row_12436
  · exact certificate.row_12437
  · exact certificate.row_12438
  · exact certificate.row_12439
  · exact certificate.row_12440
  · exact certificate.row_12441
  · exact certificate.row_12442
  · exact certificate.row_12443
  · exact certificate.row_12444
  · exact certificate.row_12445
  · exact certificate.row_12446
  · exact certificate.row_12447
  · exact certificate.row_12448
  · exact certificate.row_12449
  · exact certificate.row_12450
  · exact certificate.row_12451
  · exact certificate.row_12452
  · exact certificate.row_12453
  · exact certificate.row_12454
  · exact certificate.row_12455
  · exact certificate.row_12456
  · exact certificate.row_12457
  · exact certificate.row_12458
  · exact certificate.row_12459
  · exact certificate.row_12460
  · exact certificate.row_12461
  · exact certificate.row_12462
  · exact certificate.row_12463
  · exact certificate.row_12464
  · exact certificate.row_12465
  · exact certificate.row_12466
  · exact certificate.row_12467
  · exact certificate.row_12468
  · exact certificate.row_12469
  · exact certificate.row_12470
  · exact certificate.row_12471
  · exact certificate.row_12472
  · exact certificate.row_12473
  · exact certificate.row_12474
  · exact certificate.row_12475
  · exact certificate.row_12476
  · exact certificate.row_12477
  · exact certificate.row_12478
  · exact certificate.row_12479

certify_sparse_rows certificate from "certificates/finite/n22/sparse.bin" inverse_file "certificates/finite/n22/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse22.binaryInverse row_fn Quartic.FiniteEndpointMetadata22Data.naturalRow nwords 198 start_index 12480 row_count 64

theorem chunk_195 (i : Fin 64) (hi : 12480+i.val < 12650) :
    xorSum ((FiniteEndpointMetadata22Data.naturalRow (12480+i.val)).map
      FiniteEndpointInverse22.binaryInverse) = 2^(12480+i.val) := by
  fin_cases i
  · exact certificate.row_12480
  · exact certificate.row_12481
  · exact certificate.row_12482
  · exact certificate.row_12483
  · exact certificate.row_12484
  · exact certificate.row_12485
  · exact certificate.row_12486
  · exact certificate.row_12487
  · exact certificate.row_12488
  · exact certificate.row_12489
  · exact certificate.row_12490
  · exact certificate.row_12491
  · exact certificate.row_12492
  · exact certificate.row_12493
  · exact certificate.row_12494
  · exact certificate.row_12495
  · exact certificate.row_12496
  · exact certificate.row_12497
  · exact certificate.row_12498
  · exact certificate.row_12499
  · exact certificate.row_12500
  · exact certificate.row_12501
  · exact certificate.row_12502
  · exact certificate.row_12503
  · exact certificate.row_12504
  · exact certificate.row_12505
  · exact certificate.row_12506
  · exact certificate.row_12507
  · exact certificate.row_12508
  · exact certificate.row_12509
  · exact certificate.row_12510
  · exact certificate.row_12511
  · exact certificate.row_12512
  · exact certificate.row_12513
  · exact certificate.row_12514
  · exact certificate.row_12515
  · exact certificate.row_12516
  · exact certificate.row_12517
  · exact certificate.row_12518
  · exact certificate.row_12519
  · exact certificate.row_12520
  · exact certificate.row_12521
  · exact certificate.row_12522
  · exact certificate.row_12523
  · exact certificate.row_12524
  · exact certificate.row_12525
  · exact certificate.row_12526
  · exact certificate.row_12527
  · exact certificate.row_12528
  · exact certificate.row_12529
  · exact certificate.row_12530
  · exact certificate.row_12531
  · exact certificate.row_12532
  · exact certificate.row_12533
  · exact certificate.row_12534
  · exact certificate.row_12535
  · exact certificate.row_12536
  · exact certificate.row_12537
  · exact certificate.row_12538
  · exact certificate.row_12539
  · exact certificate.row_12540
  · exact certificate.row_12541
  · exact certificate.row_12542
  · exact certificate.row_12543

certify_sparse_rows certificate from "certificates/finite/n22/sparse.bin" inverse_file "certificates/finite/n22/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse22.binaryInverse row_fn Quartic.FiniteEndpointMetadata22Data.naturalRow nwords 198 start_index 12544 row_count 64

theorem chunk_196 (i : Fin 64) (hi : 12544+i.val < 12650) :
    xorSum ((FiniteEndpointMetadata22Data.naturalRow (12544+i.val)).map
      FiniteEndpointInverse22.binaryInverse) = 2^(12544+i.val) := by
  fin_cases i
  · exact certificate.row_12544
  · exact certificate.row_12545
  · exact certificate.row_12546
  · exact certificate.row_12547
  · exact certificate.row_12548
  · exact certificate.row_12549
  · exact certificate.row_12550
  · exact certificate.row_12551
  · exact certificate.row_12552
  · exact certificate.row_12553
  · exact certificate.row_12554
  · exact certificate.row_12555
  · exact certificate.row_12556
  · exact certificate.row_12557
  · exact certificate.row_12558
  · exact certificate.row_12559
  · exact certificate.row_12560
  · exact certificate.row_12561
  · exact certificate.row_12562
  · exact certificate.row_12563
  · exact certificate.row_12564
  · exact certificate.row_12565
  · exact certificate.row_12566
  · exact certificate.row_12567
  · exact certificate.row_12568
  · exact certificate.row_12569
  · exact certificate.row_12570
  · exact certificate.row_12571
  · exact certificate.row_12572
  · exact certificate.row_12573
  · exact certificate.row_12574
  · exact certificate.row_12575
  · exact certificate.row_12576
  · exact certificate.row_12577
  · exact certificate.row_12578
  · exact certificate.row_12579
  · exact certificate.row_12580
  · exact certificate.row_12581
  · exact certificate.row_12582
  · exact certificate.row_12583
  · exact certificate.row_12584
  · exact certificate.row_12585
  · exact certificate.row_12586
  · exact certificate.row_12587
  · exact certificate.row_12588
  · exact certificate.row_12589
  · exact certificate.row_12590
  · exact certificate.row_12591
  · exact certificate.row_12592
  · exact certificate.row_12593
  · exact certificate.row_12594
  · exact certificate.row_12595
  · exact certificate.row_12596
  · exact certificate.row_12597
  · exact certificate.row_12598
  · exact certificate.row_12599
  · exact certificate.row_12600
  · exact certificate.row_12601
  · exact certificate.row_12602
  · exact certificate.row_12603
  · exact certificate.row_12604
  · exact certificate.row_12605
  · exact certificate.row_12606
  · exact certificate.row_12607

certify_sparse_rows certificate from "certificates/finite/n22/sparse.bin" inverse_file "certificates/finite/n22/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse22.binaryInverse row_fn Quartic.FiniteEndpointMetadata22Data.naturalRow nwords 198 start_index 12608 row_count 42

theorem chunk_197 (i : Fin 64) (hi : 12608+i.val < 12650) :
    xorSum ((FiniteEndpointMetadata22Data.naturalRow (12608+i.val)).map
      FiniteEndpointInverse22.binaryInverse) = 2^(12608+i.val) := by
  fin_cases i
  · exact certificate.row_12608
  · exact certificate.row_12609
  · exact certificate.row_12610
  · exact certificate.row_12611
  · exact certificate.row_12612
  · exact certificate.row_12613
  · exact certificate.row_12614
  · exact certificate.row_12615
  · exact certificate.row_12616
  · exact certificate.row_12617
  · exact certificate.row_12618
  · exact certificate.row_12619
  · exact certificate.row_12620
  · exact certificate.row_12621
  · exact certificate.row_12622
  · exact certificate.row_12623
  · exact certificate.row_12624
  · exact certificate.row_12625
  · exact certificate.row_12626
  · exact certificate.row_12627
  · exact certificate.row_12628
  · exact certificate.row_12629
  · exact certificate.row_12630
  · exact certificate.row_12631
  · exact certificate.row_12632
  · exact certificate.row_12633
  · exact certificate.row_12634
  · exact certificate.row_12635
  · exact certificate.row_12636
  · exact certificate.row_12637
  · exact certificate.row_12638
  · exact certificate.row_12639
  · exact certificate.row_12640
  · exact certificate.row_12641
  · exact certificate.row_12642
  · exact certificate.row_12643
  · exact certificate.row_12644
  · exact certificate.row_12645
  · exact certificate.row_12646
  · exact certificate.row_12647
  · exact certificate.row_12648
  · exact certificate.row_12649
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

end Quartic.FiniteEndpointRows22
