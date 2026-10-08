import Quartic.FiniteEndpointInverseMemo24
import Quartic.FiniteEndpointMetadata24Data

/-! Kernel-checked rows of the actual quartic multiplication matrix. -/
namespace Quartic.FiniteEndpointRows24
open FiniteEndpointChecker
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 64000000

certify_sparse_rows certificate from "certificates/finite/n24/sparse.bin" inverse_file "certificates/finite/n24/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse24.binaryInverse row_fn Quartic.FiniteEndpointMetadata24Data.naturalRow nwords 275 start_index 17408 row_count 64

theorem chunk_272 (i : Fin 64) (hi : 17408+i.val < 17550) :
    xorSum ((FiniteEndpointMetadata24Data.naturalRow (17408+i.val)).map
      FiniteEndpointInverse24.binaryInverse) = 2^(17408+i.val) := by
  fin_cases i
  · exact certificate.row_17408
  · exact certificate.row_17409
  · exact certificate.row_17410
  · exact certificate.row_17411
  · exact certificate.row_17412
  · exact certificate.row_17413
  · exact certificate.row_17414
  · exact certificate.row_17415
  · exact certificate.row_17416
  · exact certificate.row_17417
  · exact certificate.row_17418
  · exact certificate.row_17419
  · exact certificate.row_17420
  · exact certificate.row_17421
  · exact certificate.row_17422
  · exact certificate.row_17423
  · exact certificate.row_17424
  · exact certificate.row_17425
  · exact certificate.row_17426
  · exact certificate.row_17427
  · exact certificate.row_17428
  · exact certificate.row_17429
  · exact certificate.row_17430
  · exact certificate.row_17431
  · exact certificate.row_17432
  · exact certificate.row_17433
  · exact certificate.row_17434
  · exact certificate.row_17435
  · exact certificate.row_17436
  · exact certificate.row_17437
  · exact certificate.row_17438
  · exact certificate.row_17439
  · exact certificate.row_17440
  · exact certificate.row_17441
  · exact certificate.row_17442
  · exact certificate.row_17443
  · exact certificate.row_17444
  · exact certificate.row_17445
  · exact certificate.row_17446
  · exact certificate.row_17447
  · exact certificate.row_17448
  · exact certificate.row_17449
  · exact certificate.row_17450
  · exact certificate.row_17451
  · exact certificate.row_17452
  · exact certificate.row_17453
  · exact certificate.row_17454
  · exact certificate.row_17455
  · exact certificate.row_17456
  · exact certificate.row_17457
  · exact certificate.row_17458
  · exact certificate.row_17459
  · exact certificate.row_17460
  · exact certificate.row_17461
  · exact certificate.row_17462
  · exact certificate.row_17463
  · exact certificate.row_17464
  · exact certificate.row_17465
  · exact certificate.row_17466
  · exact certificate.row_17467
  · exact certificate.row_17468
  · exact certificate.row_17469
  · exact certificate.row_17470
  · exact certificate.row_17471

certify_sparse_rows certificate from "certificates/finite/n24/sparse.bin" inverse_file "certificates/finite/n24/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse24.binaryInverse row_fn Quartic.FiniteEndpointMetadata24Data.naturalRow nwords 275 start_index 17472 row_count 64

theorem chunk_273 (i : Fin 64) (hi : 17472+i.val < 17550) :
    xorSum ((FiniteEndpointMetadata24Data.naturalRow (17472+i.val)).map
      FiniteEndpointInverse24.binaryInverse) = 2^(17472+i.val) := by
  fin_cases i
  · exact certificate.row_17472
  · exact certificate.row_17473
  · exact certificate.row_17474
  · exact certificate.row_17475
  · exact certificate.row_17476
  · exact certificate.row_17477
  · exact certificate.row_17478
  · exact certificate.row_17479
  · exact certificate.row_17480
  · exact certificate.row_17481
  · exact certificate.row_17482
  · exact certificate.row_17483
  · exact certificate.row_17484
  · exact certificate.row_17485
  · exact certificate.row_17486
  · exact certificate.row_17487
  · exact certificate.row_17488
  · exact certificate.row_17489
  · exact certificate.row_17490
  · exact certificate.row_17491
  · exact certificate.row_17492
  · exact certificate.row_17493
  · exact certificate.row_17494
  · exact certificate.row_17495
  · exact certificate.row_17496
  · exact certificate.row_17497
  · exact certificate.row_17498
  · exact certificate.row_17499
  · exact certificate.row_17500
  · exact certificate.row_17501
  · exact certificate.row_17502
  · exact certificate.row_17503
  · exact certificate.row_17504
  · exact certificate.row_17505
  · exact certificate.row_17506
  · exact certificate.row_17507
  · exact certificate.row_17508
  · exact certificate.row_17509
  · exact certificate.row_17510
  · exact certificate.row_17511
  · exact certificate.row_17512
  · exact certificate.row_17513
  · exact certificate.row_17514
  · exact certificate.row_17515
  · exact certificate.row_17516
  · exact certificate.row_17517
  · exact certificate.row_17518
  · exact certificate.row_17519
  · exact certificate.row_17520
  · exact certificate.row_17521
  · exact certificate.row_17522
  · exact certificate.row_17523
  · exact certificate.row_17524
  · exact certificate.row_17525
  · exact certificate.row_17526
  · exact certificate.row_17527
  · exact certificate.row_17528
  · exact certificate.row_17529
  · exact certificate.row_17530
  · exact certificate.row_17531
  · exact certificate.row_17532
  · exact certificate.row_17533
  · exact certificate.row_17534
  · exact certificate.row_17535

certify_sparse_rows certificate from "certificates/finite/n24/sparse.bin" inverse_file "certificates/finite/n24/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse24.binaryInverse row_fn Quartic.FiniteEndpointMetadata24Data.naturalRow nwords 275 start_index 17536 row_count 14

theorem chunk_274 (i : Fin 64) (hi : 17536+i.val < 17550) :
    xorSum ((FiniteEndpointMetadata24Data.naturalRow (17536+i.val)).map
      FiniteEndpointInverse24.binaryInverse) = 2^(17536+i.val) := by
  fin_cases i
  · exact certificate.row_17536
  · exact certificate.row_17537
  · exact certificate.row_17538
  · exact certificate.row_17539
  · exact certificate.row_17540
  · exact certificate.row_17541
  · exact certificate.row_17542
  · exact certificate.row_17543
  · exact certificate.row_17544
  · exact certificate.row_17545
  · exact certificate.row_17546
  · exact certificate.row_17547
  · exact certificate.row_17548
  · exact certificate.row_17549
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

end Quartic.FiniteEndpointRows24
