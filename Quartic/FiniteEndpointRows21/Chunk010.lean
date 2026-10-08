import Quartic.FiniteEndpointInverseMemo21
import Quartic.FiniteEndpointMetadata21Data

/-! Kernel-checked rows of the actual quartic multiplication matrix. -/
namespace Quartic.FiniteEndpointRows21
open FiniteEndpointChecker
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 64000000

certify_sparse_rows certificate from "certificates/finite/n21/sparse.bin" inverse_file "certificates/finite/n21/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse21.binaryInverse row_fn Quartic.FiniteEndpointMetadata21Data.naturalRow nwords 167 start_index 10240 row_count 64

theorem chunk_160 (i : Fin 64) (hi : 10240+i.val < 10626) :
    xorSum ((FiniteEndpointMetadata21Data.naturalRow (10240+i.val)).map
      FiniteEndpointInverse21.binaryInverse) = 2^(10240+i.val) := by
  fin_cases i
  · exact certificate.row_10240
  · exact certificate.row_10241
  · exact certificate.row_10242
  · exact certificate.row_10243
  · exact certificate.row_10244
  · exact certificate.row_10245
  · exact certificate.row_10246
  · exact certificate.row_10247
  · exact certificate.row_10248
  · exact certificate.row_10249
  · exact certificate.row_10250
  · exact certificate.row_10251
  · exact certificate.row_10252
  · exact certificate.row_10253
  · exact certificate.row_10254
  · exact certificate.row_10255
  · exact certificate.row_10256
  · exact certificate.row_10257
  · exact certificate.row_10258
  · exact certificate.row_10259
  · exact certificate.row_10260
  · exact certificate.row_10261
  · exact certificate.row_10262
  · exact certificate.row_10263
  · exact certificate.row_10264
  · exact certificate.row_10265
  · exact certificate.row_10266
  · exact certificate.row_10267
  · exact certificate.row_10268
  · exact certificate.row_10269
  · exact certificate.row_10270
  · exact certificate.row_10271
  · exact certificate.row_10272
  · exact certificate.row_10273
  · exact certificate.row_10274
  · exact certificate.row_10275
  · exact certificate.row_10276
  · exact certificate.row_10277
  · exact certificate.row_10278
  · exact certificate.row_10279
  · exact certificate.row_10280
  · exact certificate.row_10281
  · exact certificate.row_10282
  · exact certificate.row_10283
  · exact certificate.row_10284
  · exact certificate.row_10285
  · exact certificate.row_10286
  · exact certificate.row_10287
  · exact certificate.row_10288
  · exact certificate.row_10289
  · exact certificate.row_10290
  · exact certificate.row_10291
  · exact certificate.row_10292
  · exact certificate.row_10293
  · exact certificate.row_10294
  · exact certificate.row_10295
  · exact certificate.row_10296
  · exact certificate.row_10297
  · exact certificate.row_10298
  · exact certificate.row_10299
  · exact certificate.row_10300
  · exact certificate.row_10301
  · exact certificate.row_10302
  · exact certificate.row_10303

certify_sparse_rows certificate from "certificates/finite/n21/sparse.bin" inverse_file "certificates/finite/n21/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse21.binaryInverse row_fn Quartic.FiniteEndpointMetadata21Data.naturalRow nwords 167 start_index 10304 row_count 64

theorem chunk_161 (i : Fin 64) (hi : 10304+i.val < 10626) :
    xorSum ((FiniteEndpointMetadata21Data.naturalRow (10304+i.val)).map
      FiniteEndpointInverse21.binaryInverse) = 2^(10304+i.val) := by
  fin_cases i
  · exact certificate.row_10304
  · exact certificate.row_10305
  · exact certificate.row_10306
  · exact certificate.row_10307
  · exact certificate.row_10308
  · exact certificate.row_10309
  · exact certificate.row_10310
  · exact certificate.row_10311
  · exact certificate.row_10312
  · exact certificate.row_10313
  · exact certificate.row_10314
  · exact certificate.row_10315
  · exact certificate.row_10316
  · exact certificate.row_10317
  · exact certificate.row_10318
  · exact certificate.row_10319
  · exact certificate.row_10320
  · exact certificate.row_10321
  · exact certificate.row_10322
  · exact certificate.row_10323
  · exact certificate.row_10324
  · exact certificate.row_10325
  · exact certificate.row_10326
  · exact certificate.row_10327
  · exact certificate.row_10328
  · exact certificate.row_10329
  · exact certificate.row_10330
  · exact certificate.row_10331
  · exact certificate.row_10332
  · exact certificate.row_10333
  · exact certificate.row_10334
  · exact certificate.row_10335
  · exact certificate.row_10336
  · exact certificate.row_10337
  · exact certificate.row_10338
  · exact certificate.row_10339
  · exact certificate.row_10340
  · exact certificate.row_10341
  · exact certificate.row_10342
  · exact certificate.row_10343
  · exact certificate.row_10344
  · exact certificate.row_10345
  · exact certificate.row_10346
  · exact certificate.row_10347
  · exact certificate.row_10348
  · exact certificate.row_10349
  · exact certificate.row_10350
  · exact certificate.row_10351
  · exact certificate.row_10352
  · exact certificate.row_10353
  · exact certificate.row_10354
  · exact certificate.row_10355
  · exact certificate.row_10356
  · exact certificate.row_10357
  · exact certificate.row_10358
  · exact certificate.row_10359
  · exact certificate.row_10360
  · exact certificate.row_10361
  · exact certificate.row_10362
  · exact certificate.row_10363
  · exact certificate.row_10364
  · exact certificate.row_10365
  · exact certificate.row_10366
  · exact certificate.row_10367

certify_sparse_rows certificate from "certificates/finite/n21/sparse.bin" inverse_file "certificates/finite/n21/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse21.binaryInverse row_fn Quartic.FiniteEndpointMetadata21Data.naturalRow nwords 167 start_index 10368 row_count 64

theorem chunk_162 (i : Fin 64) (hi : 10368+i.val < 10626) :
    xorSum ((FiniteEndpointMetadata21Data.naturalRow (10368+i.val)).map
      FiniteEndpointInverse21.binaryInverse) = 2^(10368+i.val) := by
  fin_cases i
  · exact certificate.row_10368
  · exact certificate.row_10369
  · exact certificate.row_10370
  · exact certificate.row_10371
  · exact certificate.row_10372
  · exact certificate.row_10373
  · exact certificate.row_10374
  · exact certificate.row_10375
  · exact certificate.row_10376
  · exact certificate.row_10377
  · exact certificate.row_10378
  · exact certificate.row_10379
  · exact certificate.row_10380
  · exact certificate.row_10381
  · exact certificate.row_10382
  · exact certificate.row_10383
  · exact certificate.row_10384
  · exact certificate.row_10385
  · exact certificate.row_10386
  · exact certificate.row_10387
  · exact certificate.row_10388
  · exact certificate.row_10389
  · exact certificate.row_10390
  · exact certificate.row_10391
  · exact certificate.row_10392
  · exact certificate.row_10393
  · exact certificate.row_10394
  · exact certificate.row_10395
  · exact certificate.row_10396
  · exact certificate.row_10397
  · exact certificate.row_10398
  · exact certificate.row_10399
  · exact certificate.row_10400
  · exact certificate.row_10401
  · exact certificate.row_10402
  · exact certificate.row_10403
  · exact certificate.row_10404
  · exact certificate.row_10405
  · exact certificate.row_10406
  · exact certificate.row_10407
  · exact certificate.row_10408
  · exact certificate.row_10409
  · exact certificate.row_10410
  · exact certificate.row_10411
  · exact certificate.row_10412
  · exact certificate.row_10413
  · exact certificate.row_10414
  · exact certificate.row_10415
  · exact certificate.row_10416
  · exact certificate.row_10417
  · exact certificate.row_10418
  · exact certificate.row_10419
  · exact certificate.row_10420
  · exact certificate.row_10421
  · exact certificate.row_10422
  · exact certificate.row_10423
  · exact certificate.row_10424
  · exact certificate.row_10425
  · exact certificate.row_10426
  · exact certificate.row_10427
  · exact certificate.row_10428
  · exact certificate.row_10429
  · exact certificate.row_10430
  · exact certificate.row_10431

certify_sparse_rows certificate from "certificates/finite/n21/sparse.bin" inverse_file "certificates/finite/n21/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse21.binaryInverse row_fn Quartic.FiniteEndpointMetadata21Data.naturalRow nwords 167 start_index 10432 row_count 64

theorem chunk_163 (i : Fin 64) (hi : 10432+i.val < 10626) :
    xorSum ((FiniteEndpointMetadata21Data.naturalRow (10432+i.val)).map
      FiniteEndpointInverse21.binaryInverse) = 2^(10432+i.val) := by
  fin_cases i
  · exact certificate.row_10432
  · exact certificate.row_10433
  · exact certificate.row_10434
  · exact certificate.row_10435
  · exact certificate.row_10436
  · exact certificate.row_10437
  · exact certificate.row_10438
  · exact certificate.row_10439
  · exact certificate.row_10440
  · exact certificate.row_10441
  · exact certificate.row_10442
  · exact certificate.row_10443
  · exact certificate.row_10444
  · exact certificate.row_10445
  · exact certificate.row_10446
  · exact certificate.row_10447
  · exact certificate.row_10448
  · exact certificate.row_10449
  · exact certificate.row_10450
  · exact certificate.row_10451
  · exact certificate.row_10452
  · exact certificate.row_10453
  · exact certificate.row_10454
  · exact certificate.row_10455
  · exact certificate.row_10456
  · exact certificate.row_10457
  · exact certificate.row_10458
  · exact certificate.row_10459
  · exact certificate.row_10460
  · exact certificate.row_10461
  · exact certificate.row_10462
  · exact certificate.row_10463
  · exact certificate.row_10464
  · exact certificate.row_10465
  · exact certificate.row_10466
  · exact certificate.row_10467
  · exact certificate.row_10468
  · exact certificate.row_10469
  · exact certificate.row_10470
  · exact certificate.row_10471
  · exact certificate.row_10472
  · exact certificate.row_10473
  · exact certificate.row_10474
  · exact certificate.row_10475
  · exact certificate.row_10476
  · exact certificate.row_10477
  · exact certificate.row_10478
  · exact certificate.row_10479
  · exact certificate.row_10480
  · exact certificate.row_10481
  · exact certificate.row_10482
  · exact certificate.row_10483
  · exact certificate.row_10484
  · exact certificate.row_10485
  · exact certificate.row_10486
  · exact certificate.row_10487
  · exact certificate.row_10488
  · exact certificate.row_10489
  · exact certificate.row_10490
  · exact certificate.row_10491
  · exact certificate.row_10492
  · exact certificate.row_10493
  · exact certificate.row_10494
  · exact certificate.row_10495

certify_sparse_rows certificate from "certificates/finite/n21/sparse.bin" inverse_file "certificates/finite/n21/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse21.binaryInverse row_fn Quartic.FiniteEndpointMetadata21Data.naturalRow nwords 167 start_index 10496 row_count 64

theorem chunk_164 (i : Fin 64) (hi : 10496+i.val < 10626) :
    xorSum ((FiniteEndpointMetadata21Data.naturalRow (10496+i.val)).map
      FiniteEndpointInverse21.binaryInverse) = 2^(10496+i.val) := by
  fin_cases i
  · exact certificate.row_10496
  · exact certificate.row_10497
  · exact certificate.row_10498
  · exact certificate.row_10499
  · exact certificate.row_10500
  · exact certificate.row_10501
  · exact certificate.row_10502
  · exact certificate.row_10503
  · exact certificate.row_10504
  · exact certificate.row_10505
  · exact certificate.row_10506
  · exact certificate.row_10507
  · exact certificate.row_10508
  · exact certificate.row_10509
  · exact certificate.row_10510
  · exact certificate.row_10511
  · exact certificate.row_10512
  · exact certificate.row_10513
  · exact certificate.row_10514
  · exact certificate.row_10515
  · exact certificate.row_10516
  · exact certificate.row_10517
  · exact certificate.row_10518
  · exact certificate.row_10519
  · exact certificate.row_10520
  · exact certificate.row_10521
  · exact certificate.row_10522
  · exact certificate.row_10523
  · exact certificate.row_10524
  · exact certificate.row_10525
  · exact certificate.row_10526
  · exact certificate.row_10527
  · exact certificate.row_10528
  · exact certificate.row_10529
  · exact certificate.row_10530
  · exact certificate.row_10531
  · exact certificate.row_10532
  · exact certificate.row_10533
  · exact certificate.row_10534
  · exact certificate.row_10535
  · exact certificate.row_10536
  · exact certificate.row_10537
  · exact certificate.row_10538
  · exact certificate.row_10539
  · exact certificate.row_10540
  · exact certificate.row_10541
  · exact certificate.row_10542
  · exact certificate.row_10543
  · exact certificate.row_10544
  · exact certificate.row_10545
  · exact certificate.row_10546
  · exact certificate.row_10547
  · exact certificate.row_10548
  · exact certificate.row_10549
  · exact certificate.row_10550
  · exact certificate.row_10551
  · exact certificate.row_10552
  · exact certificate.row_10553
  · exact certificate.row_10554
  · exact certificate.row_10555
  · exact certificate.row_10556
  · exact certificate.row_10557
  · exact certificate.row_10558
  · exact certificate.row_10559

certify_sparse_rows certificate from "certificates/finite/n21/sparse.bin" inverse_file "certificates/finite/n21/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse21.binaryInverse row_fn Quartic.FiniteEndpointMetadata21Data.naturalRow nwords 167 start_index 10560 row_count 64

theorem chunk_165 (i : Fin 64) (hi : 10560+i.val < 10626) :
    xorSum ((FiniteEndpointMetadata21Data.naturalRow (10560+i.val)).map
      FiniteEndpointInverse21.binaryInverse) = 2^(10560+i.val) := by
  fin_cases i
  · exact certificate.row_10560
  · exact certificate.row_10561
  · exact certificate.row_10562
  · exact certificate.row_10563
  · exact certificate.row_10564
  · exact certificate.row_10565
  · exact certificate.row_10566
  · exact certificate.row_10567
  · exact certificate.row_10568
  · exact certificate.row_10569
  · exact certificate.row_10570
  · exact certificate.row_10571
  · exact certificate.row_10572
  · exact certificate.row_10573
  · exact certificate.row_10574
  · exact certificate.row_10575
  · exact certificate.row_10576
  · exact certificate.row_10577
  · exact certificate.row_10578
  · exact certificate.row_10579
  · exact certificate.row_10580
  · exact certificate.row_10581
  · exact certificate.row_10582
  · exact certificate.row_10583
  · exact certificate.row_10584
  · exact certificate.row_10585
  · exact certificate.row_10586
  · exact certificate.row_10587
  · exact certificate.row_10588
  · exact certificate.row_10589
  · exact certificate.row_10590
  · exact certificate.row_10591
  · exact certificate.row_10592
  · exact certificate.row_10593
  · exact certificate.row_10594
  · exact certificate.row_10595
  · exact certificate.row_10596
  · exact certificate.row_10597
  · exact certificate.row_10598
  · exact certificate.row_10599
  · exact certificate.row_10600
  · exact certificate.row_10601
  · exact certificate.row_10602
  · exact certificate.row_10603
  · exact certificate.row_10604
  · exact certificate.row_10605
  · exact certificate.row_10606
  · exact certificate.row_10607
  · exact certificate.row_10608
  · exact certificate.row_10609
  · exact certificate.row_10610
  · exact certificate.row_10611
  · exact certificate.row_10612
  · exact certificate.row_10613
  · exact certificate.row_10614
  · exact certificate.row_10615
  · exact certificate.row_10616
  · exact certificate.row_10617
  · exact certificate.row_10618
  · exact certificate.row_10619
  · exact certificate.row_10620
  · exact certificate.row_10621
  · exact certificate.row_10622
  · exact certificate.row_10623

certify_sparse_rows certificate from "certificates/finite/n21/sparse.bin" inverse_file "certificates/finite/n21/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse21.binaryInverse row_fn Quartic.FiniteEndpointMetadata21Data.naturalRow nwords 167 start_index 10624 row_count 2

theorem chunk_166 (i : Fin 64) (hi : 10624+i.val < 10626) :
    xorSum ((FiniteEndpointMetadata21Data.naturalRow (10624+i.val)).map
      FiniteEndpointInverse21.binaryInverse) = 2^(10624+i.val) := by
  fin_cases i
  · exact certificate.row_10624
  · exact certificate.row_10625
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
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi

end Quartic.FiniteEndpointRows21
