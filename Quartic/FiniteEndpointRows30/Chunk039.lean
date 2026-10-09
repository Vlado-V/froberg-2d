module

public import Quartic.FiniteEndpointInverseMemo30
import Quartic.FiniteEndpointRows30.Chunk033
public import Quartic.FiniteEndpointMetadata30Data

@[expose] public section

/-! Kernel-checked rows of the actual quartic multiplication matrix. -/
namespace Quartic.FiniteEndpointRows30
open FiniteEndpointChecker
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 64000000

certify_sparse_rows certificate from "certificates/finite/n30/sparse.bin" inverse_file "certificates/finite/n30/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse30.binaryInverse row_fn Quartic.FiniteEndpointMetadata30Data.naturalRow nwords 640 start_index 39936 row_count 64

theorem chunk_624 (i : Fin 64) (hi : 39936+i.val < 40920) :
    xorSum ((FiniteEndpointMetadata30Data.naturalRow (39936+i.val)).map
      FiniteEndpointInverse30.binaryInverse) = 2^(39936+i.val) := by
  fin_cases i
  · exact certificate.row_39936
  · exact certificate.row_39937
  · exact certificate.row_39938
  · exact certificate.row_39939
  · exact certificate.row_39940
  · exact certificate.row_39941
  · exact certificate.row_39942
  · exact certificate.row_39943
  · exact certificate.row_39944
  · exact certificate.row_39945
  · exact certificate.row_39946
  · exact certificate.row_39947
  · exact certificate.row_39948
  · exact certificate.row_39949
  · exact certificate.row_39950
  · exact certificate.row_39951
  · exact certificate.row_39952
  · exact certificate.row_39953
  · exact certificate.row_39954
  · exact certificate.row_39955
  · exact certificate.row_39956
  · exact certificate.row_39957
  · exact certificate.row_39958
  · exact certificate.row_39959
  · exact certificate.row_39960
  · exact certificate.row_39961
  · exact certificate.row_39962
  · exact certificate.row_39963
  · exact certificate.row_39964
  · exact certificate.row_39965
  · exact certificate.row_39966
  · exact certificate.row_39967
  · exact certificate.row_39968
  · exact certificate.row_39969
  · exact certificate.row_39970
  · exact certificate.row_39971
  · exact certificate.row_39972
  · exact certificate.row_39973
  · exact certificate.row_39974
  · exact certificate.row_39975
  · exact certificate.row_39976
  · exact certificate.row_39977
  · exact certificate.row_39978
  · exact certificate.row_39979
  · exact certificate.row_39980
  · exact certificate.row_39981
  · exact certificate.row_39982
  · exact certificate.row_39983
  · exact certificate.row_39984
  · exact certificate.row_39985
  · exact certificate.row_39986
  · exact certificate.row_39987
  · exact certificate.row_39988
  · exact certificate.row_39989
  · exact certificate.row_39990
  · exact certificate.row_39991
  · exact certificate.row_39992
  · exact certificate.row_39993
  · exact certificate.row_39994
  · exact certificate.row_39995
  · exact certificate.row_39996
  · exact certificate.row_39997
  · exact certificate.row_39998
  · exact certificate.row_39999

certify_sparse_rows certificate from "certificates/finite/n30/sparse.bin" inverse_file "certificates/finite/n30/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse30.binaryInverse row_fn Quartic.FiniteEndpointMetadata30Data.naturalRow nwords 640 start_index 40000 row_count 64

theorem chunk_625 (i : Fin 64) (hi : 40000+i.val < 40920) :
    xorSum ((FiniteEndpointMetadata30Data.naturalRow (40000+i.val)).map
      FiniteEndpointInverse30.binaryInverse) = 2^(40000+i.val) := by
  fin_cases i
  · exact certificate.row_40000
  · exact certificate.row_40001
  · exact certificate.row_40002
  · exact certificate.row_40003
  · exact certificate.row_40004
  · exact certificate.row_40005
  · exact certificate.row_40006
  · exact certificate.row_40007
  · exact certificate.row_40008
  · exact certificate.row_40009
  · exact certificate.row_40010
  · exact certificate.row_40011
  · exact certificate.row_40012
  · exact certificate.row_40013
  · exact certificate.row_40014
  · exact certificate.row_40015
  · exact certificate.row_40016
  · exact certificate.row_40017
  · exact certificate.row_40018
  · exact certificate.row_40019
  · exact certificate.row_40020
  · exact certificate.row_40021
  · exact certificate.row_40022
  · exact certificate.row_40023
  · exact certificate.row_40024
  · exact certificate.row_40025
  · exact certificate.row_40026
  · exact certificate.row_40027
  · exact certificate.row_40028
  · exact certificate.row_40029
  · exact certificate.row_40030
  · exact certificate.row_40031
  · exact certificate.row_40032
  · exact certificate.row_40033
  · exact certificate.row_40034
  · exact certificate.row_40035
  · exact certificate.row_40036
  · exact certificate.row_40037
  · exact certificate.row_40038
  · exact certificate.row_40039
  · exact certificate.row_40040
  · exact certificate.row_40041
  · exact certificate.row_40042
  · exact certificate.row_40043
  · exact certificate.row_40044
  · exact certificate.row_40045
  · exact certificate.row_40046
  · exact certificate.row_40047
  · exact certificate.row_40048
  · exact certificate.row_40049
  · exact certificate.row_40050
  · exact certificate.row_40051
  · exact certificate.row_40052
  · exact certificate.row_40053
  · exact certificate.row_40054
  · exact certificate.row_40055
  · exact certificate.row_40056
  · exact certificate.row_40057
  · exact certificate.row_40058
  · exact certificate.row_40059
  · exact certificate.row_40060
  · exact certificate.row_40061
  · exact certificate.row_40062
  · exact certificate.row_40063

certify_sparse_rows certificate from "certificates/finite/n30/sparse.bin" inverse_file "certificates/finite/n30/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse30.binaryInverse row_fn Quartic.FiniteEndpointMetadata30Data.naturalRow nwords 640 start_index 40064 row_count 64

theorem chunk_626 (i : Fin 64) (hi : 40064+i.val < 40920) :
    xorSum ((FiniteEndpointMetadata30Data.naturalRow (40064+i.val)).map
      FiniteEndpointInverse30.binaryInverse) = 2^(40064+i.val) := by
  fin_cases i
  · exact certificate.row_40064
  · exact certificate.row_40065
  · exact certificate.row_40066
  · exact certificate.row_40067
  · exact certificate.row_40068
  · exact certificate.row_40069
  · exact certificate.row_40070
  · exact certificate.row_40071
  · exact certificate.row_40072
  · exact certificate.row_40073
  · exact certificate.row_40074
  · exact certificate.row_40075
  · exact certificate.row_40076
  · exact certificate.row_40077
  · exact certificate.row_40078
  · exact certificate.row_40079
  · exact certificate.row_40080
  · exact certificate.row_40081
  · exact certificate.row_40082
  · exact certificate.row_40083
  · exact certificate.row_40084
  · exact certificate.row_40085
  · exact certificate.row_40086
  · exact certificate.row_40087
  · exact certificate.row_40088
  · exact certificate.row_40089
  · exact certificate.row_40090
  · exact certificate.row_40091
  · exact certificate.row_40092
  · exact certificate.row_40093
  · exact certificate.row_40094
  · exact certificate.row_40095
  · exact certificate.row_40096
  · exact certificate.row_40097
  · exact certificate.row_40098
  · exact certificate.row_40099
  · exact certificate.row_40100
  · exact certificate.row_40101
  · exact certificate.row_40102
  · exact certificate.row_40103
  · exact certificate.row_40104
  · exact certificate.row_40105
  · exact certificate.row_40106
  · exact certificate.row_40107
  · exact certificate.row_40108
  · exact certificate.row_40109
  · exact certificate.row_40110
  · exact certificate.row_40111
  · exact certificate.row_40112
  · exact certificate.row_40113
  · exact certificate.row_40114
  · exact certificate.row_40115
  · exact certificate.row_40116
  · exact certificate.row_40117
  · exact certificate.row_40118
  · exact certificate.row_40119
  · exact certificate.row_40120
  · exact certificate.row_40121
  · exact certificate.row_40122
  · exact certificate.row_40123
  · exact certificate.row_40124
  · exact certificate.row_40125
  · exact certificate.row_40126
  · exact certificate.row_40127

certify_sparse_rows certificate from "certificates/finite/n30/sparse.bin" inverse_file "certificates/finite/n30/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse30.binaryInverse row_fn Quartic.FiniteEndpointMetadata30Data.naturalRow nwords 640 start_index 40128 row_count 64

theorem chunk_627 (i : Fin 64) (hi : 40128+i.val < 40920) :
    xorSum ((FiniteEndpointMetadata30Data.naturalRow (40128+i.val)).map
      FiniteEndpointInverse30.binaryInverse) = 2^(40128+i.val) := by
  fin_cases i
  · exact certificate.row_40128
  · exact certificate.row_40129
  · exact certificate.row_40130
  · exact certificate.row_40131
  · exact certificate.row_40132
  · exact certificate.row_40133
  · exact certificate.row_40134
  · exact certificate.row_40135
  · exact certificate.row_40136
  · exact certificate.row_40137
  · exact certificate.row_40138
  · exact certificate.row_40139
  · exact certificate.row_40140
  · exact certificate.row_40141
  · exact certificate.row_40142
  · exact certificate.row_40143
  · exact certificate.row_40144
  · exact certificate.row_40145
  · exact certificate.row_40146
  · exact certificate.row_40147
  · exact certificate.row_40148
  · exact certificate.row_40149
  · exact certificate.row_40150
  · exact certificate.row_40151
  · exact certificate.row_40152
  · exact certificate.row_40153
  · exact certificate.row_40154
  · exact certificate.row_40155
  · exact certificate.row_40156
  · exact certificate.row_40157
  · exact certificate.row_40158
  · exact certificate.row_40159
  · exact certificate.row_40160
  · exact certificate.row_40161
  · exact certificate.row_40162
  · exact certificate.row_40163
  · exact certificate.row_40164
  · exact certificate.row_40165
  · exact certificate.row_40166
  · exact certificate.row_40167
  · exact certificate.row_40168
  · exact certificate.row_40169
  · exact certificate.row_40170
  · exact certificate.row_40171
  · exact certificate.row_40172
  · exact certificate.row_40173
  · exact certificate.row_40174
  · exact certificate.row_40175
  · exact certificate.row_40176
  · exact certificate.row_40177
  · exact certificate.row_40178
  · exact certificate.row_40179
  · exact certificate.row_40180
  · exact certificate.row_40181
  · exact certificate.row_40182
  · exact certificate.row_40183
  · exact certificate.row_40184
  · exact certificate.row_40185
  · exact certificate.row_40186
  · exact certificate.row_40187
  · exact certificate.row_40188
  · exact certificate.row_40189
  · exact certificate.row_40190
  · exact certificate.row_40191

certify_sparse_rows certificate from "certificates/finite/n30/sparse.bin" inverse_file "certificates/finite/n30/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse30.binaryInverse row_fn Quartic.FiniteEndpointMetadata30Data.naturalRow nwords 640 start_index 40192 row_count 64

theorem chunk_628 (i : Fin 64) (hi : 40192+i.val < 40920) :
    xorSum ((FiniteEndpointMetadata30Data.naturalRow (40192+i.val)).map
      FiniteEndpointInverse30.binaryInverse) = 2^(40192+i.val) := by
  fin_cases i
  · exact certificate.row_40192
  · exact certificate.row_40193
  · exact certificate.row_40194
  · exact certificate.row_40195
  · exact certificate.row_40196
  · exact certificate.row_40197
  · exact certificate.row_40198
  · exact certificate.row_40199
  · exact certificate.row_40200
  · exact certificate.row_40201
  · exact certificate.row_40202
  · exact certificate.row_40203
  · exact certificate.row_40204
  · exact certificate.row_40205
  · exact certificate.row_40206
  · exact certificate.row_40207
  · exact certificate.row_40208
  · exact certificate.row_40209
  · exact certificate.row_40210
  · exact certificate.row_40211
  · exact certificate.row_40212
  · exact certificate.row_40213
  · exact certificate.row_40214
  · exact certificate.row_40215
  · exact certificate.row_40216
  · exact certificate.row_40217
  · exact certificate.row_40218
  · exact certificate.row_40219
  · exact certificate.row_40220
  · exact certificate.row_40221
  · exact certificate.row_40222
  · exact certificate.row_40223
  · exact certificate.row_40224
  · exact certificate.row_40225
  · exact certificate.row_40226
  · exact certificate.row_40227
  · exact certificate.row_40228
  · exact certificate.row_40229
  · exact certificate.row_40230
  · exact certificate.row_40231
  · exact certificate.row_40232
  · exact certificate.row_40233
  · exact certificate.row_40234
  · exact certificate.row_40235
  · exact certificate.row_40236
  · exact certificate.row_40237
  · exact certificate.row_40238
  · exact certificate.row_40239
  · exact certificate.row_40240
  · exact certificate.row_40241
  · exact certificate.row_40242
  · exact certificate.row_40243
  · exact certificate.row_40244
  · exact certificate.row_40245
  · exact certificate.row_40246
  · exact certificate.row_40247
  · exact certificate.row_40248
  · exact certificate.row_40249
  · exact certificate.row_40250
  · exact certificate.row_40251
  · exact certificate.row_40252
  · exact certificate.row_40253
  · exact certificate.row_40254
  · exact certificate.row_40255

certify_sparse_rows certificate from "certificates/finite/n30/sparse.bin" inverse_file "certificates/finite/n30/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse30.binaryInverse row_fn Quartic.FiniteEndpointMetadata30Data.naturalRow nwords 640 start_index 40256 row_count 64

theorem chunk_629 (i : Fin 64) (hi : 40256+i.val < 40920) :
    xorSum ((FiniteEndpointMetadata30Data.naturalRow (40256+i.val)).map
      FiniteEndpointInverse30.binaryInverse) = 2^(40256+i.val) := by
  fin_cases i
  · exact certificate.row_40256
  · exact certificate.row_40257
  · exact certificate.row_40258
  · exact certificate.row_40259
  · exact certificate.row_40260
  · exact certificate.row_40261
  · exact certificate.row_40262
  · exact certificate.row_40263
  · exact certificate.row_40264
  · exact certificate.row_40265
  · exact certificate.row_40266
  · exact certificate.row_40267
  · exact certificate.row_40268
  · exact certificate.row_40269
  · exact certificate.row_40270
  · exact certificate.row_40271
  · exact certificate.row_40272
  · exact certificate.row_40273
  · exact certificate.row_40274
  · exact certificate.row_40275
  · exact certificate.row_40276
  · exact certificate.row_40277
  · exact certificate.row_40278
  · exact certificate.row_40279
  · exact certificate.row_40280
  · exact certificate.row_40281
  · exact certificate.row_40282
  · exact certificate.row_40283
  · exact certificate.row_40284
  · exact certificate.row_40285
  · exact certificate.row_40286
  · exact certificate.row_40287
  · exact certificate.row_40288
  · exact certificate.row_40289
  · exact certificate.row_40290
  · exact certificate.row_40291
  · exact certificate.row_40292
  · exact certificate.row_40293
  · exact certificate.row_40294
  · exact certificate.row_40295
  · exact certificate.row_40296
  · exact certificate.row_40297
  · exact certificate.row_40298
  · exact certificate.row_40299
  · exact certificate.row_40300
  · exact certificate.row_40301
  · exact certificate.row_40302
  · exact certificate.row_40303
  · exact certificate.row_40304
  · exact certificate.row_40305
  · exact certificate.row_40306
  · exact certificate.row_40307
  · exact certificate.row_40308
  · exact certificate.row_40309
  · exact certificate.row_40310
  · exact certificate.row_40311
  · exact certificate.row_40312
  · exact certificate.row_40313
  · exact certificate.row_40314
  · exact certificate.row_40315
  · exact certificate.row_40316
  · exact certificate.row_40317
  · exact certificate.row_40318
  · exact certificate.row_40319

certify_sparse_rows certificate from "certificates/finite/n30/sparse.bin" inverse_file "certificates/finite/n30/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse30.binaryInverse row_fn Quartic.FiniteEndpointMetadata30Data.naturalRow nwords 640 start_index 40320 row_count 64

theorem chunk_630 (i : Fin 64) (hi : 40320+i.val < 40920) :
    xorSum ((FiniteEndpointMetadata30Data.naturalRow (40320+i.val)).map
      FiniteEndpointInverse30.binaryInverse) = 2^(40320+i.val) := by
  fin_cases i
  · exact certificate.row_40320
  · exact certificate.row_40321
  · exact certificate.row_40322
  · exact certificate.row_40323
  · exact certificate.row_40324
  · exact certificate.row_40325
  · exact certificate.row_40326
  · exact certificate.row_40327
  · exact certificate.row_40328
  · exact certificate.row_40329
  · exact certificate.row_40330
  · exact certificate.row_40331
  · exact certificate.row_40332
  · exact certificate.row_40333
  · exact certificate.row_40334
  · exact certificate.row_40335
  · exact certificate.row_40336
  · exact certificate.row_40337
  · exact certificate.row_40338
  · exact certificate.row_40339
  · exact certificate.row_40340
  · exact certificate.row_40341
  · exact certificate.row_40342
  · exact certificate.row_40343
  · exact certificate.row_40344
  · exact certificate.row_40345
  · exact certificate.row_40346
  · exact certificate.row_40347
  · exact certificate.row_40348
  · exact certificate.row_40349
  · exact certificate.row_40350
  · exact certificate.row_40351
  · exact certificate.row_40352
  · exact certificate.row_40353
  · exact certificate.row_40354
  · exact certificate.row_40355
  · exact certificate.row_40356
  · exact certificate.row_40357
  · exact certificate.row_40358
  · exact certificate.row_40359
  · exact certificate.row_40360
  · exact certificate.row_40361
  · exact certificate.row_40362
  · exact certificate.row_40363
  · exact certificate.row_40364
  · exact certificate.row_40365
  · exact certificate.row_40366
  · exact certificate.row_40367
  · exact certificate.row_40368
  · exact certificate.row_40369
  · exact certificate.row_40370
  · exact certificate.row_40371
  · exact certificate.row_40372
  · exact certificate.row_40373
  · exact certificate.row_40374
  · exact certificate.row_40375
  · exact certificate.row_40376
  · exact certificate.row_40377
  · exact certificate.row_40378
  · exact certificate.row_40379
  · exact certificate.row_40380
  · exact certificate.row_40381
  · exact certificate.row_40382
  · exact certificate.row_40383

certify_sparse_rows certificate from "certificates/finite/n30/sparse.bin" inverse_file "certificates/finite/n30/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse30.binaryInverse row_fn Quartic.FiniteEndpointMetadata30Data.naturalRow nwords 640 start_index 40384 row_count 64

theorem chunk_631 (i : Fin 64) (hi : 40384+i.val < 40920) :
    xorSum ((FiniteEndpointMetadata30Data.naturalRow (40384+i.val)).map
      FiniteEndpointInverse30.binaryInverse) = 2^(40384+i.val) := by
  fin_cases i
  · exact certificate.row_40384
  · exact certificate.row_40385
  · exact certificate.row_40386
  · exact certificate.row_40387
  · exact certificate.row_40388
  · exact certificate.row_40389
  · exact certificate.row_40390
  · exact certificate.row_40391
  · exact certificate.row_40392
  · exact certificate.row_40393
  · exact certificate.row_40394
  · exact certificate.row_40395
  · exact certificate.row_40396
  · exact certificate.row_40397
  · exact certificate.row_40398
  · exact certificate.row_40399
  · exact certificate.row_40400
  · exact certificate.row_40401
  · exact certificate.row_40402
  · exact certificate.row_40403
  · exact certificate.row_40404
  · exact certificate.row_40405
  · exact certificate.row_40406
  · exact certificate.row_40407
  · exact certificate.row_40408
  · exact certificate.row_40409
  · exact certificate.row_40410
  · exact certificate.row_40411
  · exact certificate.row_40412
  · exact certificate.row_40413
  · exact certificate.row_40414
  · exact certificate.row_40415
  · exact certificate.row_40416
  · exact certificate.row_40417
  · exact certificate.row_40418
  · exact certificate.row_40419
  · exact certificate.row_40420
  · exact certificate.row_40421
  · exact certificate.row_40422
  · exact certificate.row_40423
  · exact certificate.row_40424
  · exact certificate.row_40425
  · exact certificate.row_40426
  · exact certificate.row_40427
  · exact certificate.row_40428
  · exact certificate.row_40429
  · exact certificate.row_40430
  · exact certificate.row_40431
  · exact certificate.row_40432
  · exact certificate.row_40433
  · exact certificate.row_40434
  · exact certificate.row_40435
  · exact certificate.row_40436
  · exact certificate.row_40437
  · exact certificate.row_40438
  · exact certificate.row_40439
  · exact certificate.row_40440
  · exact certificate.row_40441
  · exact certificate.row_40442
  · exact certificate.row_40443
  · exact certificate.row_40444
  · exact certificate.row_40445
  · exact certificate.row_40446
  · exact certificate.row_40447

certify_sparse_rows certificate from "certificates/finite/n30/sparse.bin" inverse_file "certificates/finite/n30/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse30.binaryInverse row_fn Quartic.FiniteEndpointMetadata30Data.naturalRow nwords 640 start_index 40448 row_count 64

theorem chunk_632 (i : Fin 64) (hi : 40448+i.val < 40920) :
    xorSum ((FiniteEndpointMetadata30Data.naturalRow (40448+i.val)).map
      FiniteEndpointInverse30.binaryInverse) = 2^(40448+i.val) := by
  fin_cases i
  · exact certificate.row_40448
  · exact certificate.row_40449
  · exact certificate.row_40450
  · exact certificate.row_40451
  · exact certificate.row_40452
  · exact certificate.row_40453
  · exact certificate.row_40454
  · exact certificate.row_40455
  · exact certificate.row_40456
  · exact certificate.row_40457
  · exact certificate.row_40458
  · exact certificate.row_40459
  · exact certificate.row_40460
  · exact certificate.row_40461
  · exact certificate.row_40462
  · exact certificate.row_40463
  · exact certificate.row_40464
  · exact certificate.row_40465
  · exact certificate.row_40466
  · exact certificate.row_40467
  · exact certificate.row_40468
  · exact certificate.row_40469
  · exact certificate.row_40470
  · exact certificate.row_40471
  · exact certificate.row_40472
  · exact certificate.row_40473
  · exact certificate.row_40474
  · exact certificate.row_40475
  · exact certificate.row_40476
  · exact certificate.row_40477
  · exact certificate.row_40478
  · exact certificate.row_40479
  · exact certificate.row_40480
  · exact certificate.row_40481
  · exact certificate.row_40482
  · exact certificate.row_40483
  · exact certificate.row_40484
  · exact certificate.row_40485
  · exact certificate.row_40486
  · exact certificate.row_40487
  · exact certificate.row_40488
  · exact certificate.row_40489
  · exact certificate.row_40490
  · exact certificate.row_40491
  · exact certificate.row_40492
  · exact certificate.row_40493
  · exact certificate.row_40494
  · exact certificate.row_40495
  · exact certificate.row_40496
  · exact certificate.row_40497
  · exact certificate.row_40498
  · exact certificate.row_40499
  · exact certificate.row_40500
  · exact certificate.row_40501
  · exact certificate.row_40502
  · exact certificate.row_40503
  · exact certificate.row_40504
  · exact certificate.row_40505
  · exact certificate.row_40506
  · exact certificate.row_40507
  · exact certificate.row_40508
  · exact certificate.row_40509
  · exact certificate.row_40510
  · exact certificate.row_40511

certify_sparse_rows certificate from "certificates/finite/n30/sparse.bin" inverse_file "certificates/finite/n30/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse30.binaryInverse row_fn Quartic.FiniteEndpointMetadata30Data.naturalRow nwords 640 start_index 40512 row_count 64

theorem chunk_633 (i : Fin 64) (hi : 40512+i.val < 40920) :
    xorSum ((FiniteEndpointMetadata30Data.naturalRow (40512+i.val)).map
      FiniteEndpointInverse30.binaryInverse) = 2^(40512+i.val) := by
  fin_cases i
  · exact certificate.row_40512
  · exact certificate.row_40513
  · exact certificate.row_40514
  · exact certificate.row_40515
  · exact certificate.row_40516
  · exact certificate.row_40517
  · exact certificate.row_40518
  · exact certificate.row_40519
  · exact certificate.row_40520
  · exact certificate.row_40521
  · exact certificate.row_40522
  · exact certificate.row_40523
  · exact certificate.row_40524
  · exact certificate.row_40525
  · exact certificate.row_40526
  · exact certificate.row_40527
  · exact certificate.row_40528
  · exact certificate.row_40529
  · exact certificate.row_40530
  · exact certificate.row_40531
  · exact certificate.row_40532
  · exact certificate.row_40533
  · exact certificate.row_40534
  · exact certificate.row_40535
  · exact certificate.row_40536
  · exact certificate.row_40537
  · exact certificate.row_40538
  · exact certificate.row_40539
  · exact certificate.row_40540
  · exact certificate.row_40541
  · exact certificate.row_40542
  · exact certificate.row_40543
  · exact certificate.row_40544
  · exact certificate.row_40545
  · exact certificate.row_40546
  · exact certificate.row_40547
  · exact certificate.row_40548
  · exact certificate.row_40549
  · exact certificate.row_40550
  · exact certificate.row_40551
  · exact certificate.row_40552
  · exact certificate.row_40553
  · exact certificate.row_40554
  · exact certificate.row_40555
  · exact certificate.row_40556
  · exact certificate.row_40557
  · exact certificate.row_40558
  · exact certificate.row_40559
  · exact certificate.row_40560
  · exact certificate.row_40561
  · exact certificate.row_40562
  · exact certificate.row_40563
  · exact certificate.row_40564
  · exact certificate.row_40565
  · exact certificate.row_40566
  · exact certificate.row_40567
  · exact certificate.row_40568
  · exact certificate.row_40569
  · exact certificate.row_40570
  · exact certificate.row_40571
  · exact certificate.row_40572
  · exact certificate.row_40573
  · exact certificate.row_40574
  · exact certificate.row_40575

certify_sparse_rows certificate from "certificates/finite/n30/sparse.bin" inverse_file "certificates/finite/n30/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse30.binaryInverse row_fn Quartic.FiniteEndpointMetadata30Data.naturalRow nwords 640 start_index 40576 row_count 64

theorem chunk_634 (i : Fin 64) (hi : 40576+i.val < 40920) :
    xorSum ((FiniteEndpointMetadata30Data.naturalRow (40576+i.val)).map
      FiniteEndpointInverse30.binaryInverse) = 2^(40576+i.val) := by
  fin_cases i
  · exact certificate.row_40576
  · exact certificate.row_40577
  · exact certificate.row_40578
  · exact certificate.row_40579
  · exact certificate.row_40580
  · exact certificate.row_40581
  · exact certificate.row_40582
  · exact certificate.row_40583
  · exact certificate.row_40584
  · exact certificate.row_40585
  · exact certificate.row_40586
  · exact certificate.row_40587
  · exact certificate.row_40588
  · exact certificate.row_40589
  · exact certificate.row_40590
  · exact certificate.row_40591
  · exact certificate.row_40592
  · exact certificate.row_40593
  · exact certificate.row_40594
  · exact certificate.row_40595
  · exact certificate.row_40596
  · exact certificate.row_40597
  · exact certificate.row_40598
  · exact certificate.row_40599
  · exact certificate.row_40600
  · exact certificate.row_40601
  · exact certificate.row_40602
  · exact certificate.row_40603
  · exact certificate.row_40604
  · exact certificate.row_40605
  · exact certificate.row_40606
  · exact certificate.row_40607
  · exact certificate.row_40608
  · exact certificate.row_40609
  · exact certificate.row_40610
  · exact certificate.row_40611
  · exact certificate.row_40612
  · exact certificate.row_40613
  · exact certificate.row_40614
  · exact certificate.row_40615
  · exact certificate.row_40616
  · exact certificate.row_40617
  · exact certificate.row_40618
  · exact certificate.row_40619
  · exact certificate.row_40620
  · exact certificate.row_40621
  · exact certificate.row_40622
  · exact certificate.row_40623
  · exact certificate.row_40624
  · exact certificate.row_40625
  · exact certificate.row_40626
  · exact certificate.row_40627
  · exact certificate.row_40628
  · exact certificate.row_40629
  · exact certificate.row_40630
  · exact certificate.row_40631
  · exact certificate.row_40632
  · exact certificate.row_40633
  · exact certificate.row_40634
  · exact certificate.row_40635
  · exact certificate.row_40636
  · exact certificate.row_40637
  · exact certificate.row_40638
  · exact certificate.row_40639

certify_sparse_rows certificate from "certificates/finite/n30/sparse.bin" inverse_file "certificates/finite/n30/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse30.binaryInverse row_fn Quartic.FiniteEndpointMetadata30Data.naturalRow nwords 640 start_index 40640 row_count 64

theorem chunk_635 (i : Fin 64) (hi : 40640+i.val < 40920) :
    xorSum ((FiniteEndpointMetadata30Data.naturalRow (40640+i.val)).map
      FiniteEndpointInverse30.binaryInverse) = 2^(40640+i.val) := by
  fin_cases i
  · exact certificate.row_40640
  · exact certificate.row_40641
  · exact certificate.row_40642
  · exact certificate.row_40643
  · exact certificate.row_40644
  · exact certificate.row_40645
  · exact certificate.row_40646
  · exact certificate.row_40647
  · exact certificate.row_40648
  · exact certificate.row_40649
  · exact certificate.row_40650
  · exact certificate.row_40651
  · exact certificate.row_40652
  · exact certificate.row_40653
  · exact certificate.row_40654
  · exact certificate.row_40655
  · exact certificate.row_40656
  · exact certificate.row_40657
  · exact certificate.row_40658
  · exact certificate.row_40659
  · exact certificate.row_40660
  · exact certificate.row_40661
  · exact certificate.row_40662
  · exact certificate.row_40663
  · exact certificate.row_40664
  · exact certificate.row_40665
  · exact certificate.row_40666
  · exact certificate.row_40667
  · exact certificate.row_40668
  · exact certificate.row_40669
  · exact certificate.row_40670
  · exact certificate.row_40671
  · exact certificate.row_40672
  · exact certificate.row_40673
  · exact certificate.row_40674
  · exact certificate.row_40675
  · exact certificate.row_40676
  · exact certificate.row_40677
  · exact certificate.row_40678
  · exact certificate.row_40679
  · exact certificate.row_40680
  · exact certificate.row_40681
  · exact certificate.row_40682
  · exact certificate.row_40683
  · exact certificate.row_40684
  · exact certificate.row_40685
  · exact certificate.row_40686
  · exact certificate.row_40687
  · exact certificate.row_40688
  · exact certificate.row_40689
  · exact certificate.row_40690
  · exact certificate.row_40691
  · exact certificate.row_40692
  · exact certificate.row_40693
  · exact certificate.row_40694
  · exact certificate.row_40695
  · exact certificate.row_40696
  · exact certificate.row_40697
  · exact certificate.row_40698
  · exact certificate.row_40699
  · exact certificate.row_40700
  · exact certificate.row_40701
  · exact certificate.row_40702
  · exact certificate.row_40703

certify_sparse_rows certificate from "certificates/finite/n30/sparse.bin" inverse_file "certificates/finite/n30/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse30.binaryInverse row_fn Quartic.FiniteEndpointMetadata30Data.naturalRow nwords 640 start_index 40704 row_count 64

theorem chunk_636 (i : Fin 64) (hi : 40704+i.val < 40920) :
    xorSum ((FiniteEndpointMetadata30Data.naturalRow (40704+i.val)).map
      FiniteEndpointInverse30.binaryInverse) = 2^(40704+i.val) := by
  fin_cases i
  · exact certificate.row_40704
  · exact certificate.row_40705
  · exact certificate.row_40706
  · exact certificate.row_40707
  · exact certificate.row_40708
  · exact certificate.row_40709
  · exact certificate.row_40710
  · exact certificate.row_40711
  · exact certificate.row_40712
  · exact certificate.row_40713
  · exact certificate.row_40714
  · exact certificate.row_40715
  · exact certificate.row_40716
  · exact certificate.row_40717
  · exact certificate.row_40718
  · exact certificate.row_40719
  · exact certificate.row_40720
  · exact certificate.row_40721
  · exact certificate.row_40722
  · exact certificate.row_40723
  · exact certificate.row_40724
  · exact certificate.row_40725
  · exact certificate.row_40726
  · exact certificate.row_40727
  · exact certificate.row_40728
  · exact certificate.row_40729
  · exact certificate.row_40730
  · exact certificate.row_40731
  · exact certificate.row_40732
  · exact certificate.row_40733
  · exact certificate.row_40734
  · exact certificate.row_40735
  · exact certificate.row_40736
  · exact certificate.row_40737
  · exact certificate.row_40738
  · exact certificate.row_40739
  · exact certificate.row_40740
  · exact certificate.row_40741
  · exact certificate.row_40742
  · exact certificate.row_40743
  · exact certificate.row_40744
  · exact certificate.row_40745
  · exact certificate.row_40746
  · exact certificate.row_40747
  · exact certificate.row_40748
  · exact certificate.row_40749
  · exact certificate.row_40750
  · exact certificate.row_40751
  · exact certificate.row_40752
  · exact certificate.row_40753
  · exact certificate.row_40754
  · exact certificate.row_40755
  · exact certificate.row_40756
  · exact certificate.row_40757
  · exact certificate.row_40758
  · exact certificate.row_40759
  · exact certificate.row_40760
  · exact certificate.row_40761
  · exact certificate.row_40762
  · exact certificate.row_40763
  · exact certificate.row_40764
  · exact certificate.row_40765
  · exact certificate.row_40766
  · exact certificate.row_40767

certify_sparse_rows certificate from "certificates/finite/n30/sparse.bin" inverse_file "certificates/finite/n30/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse30.binaryInverse row_fn Quartic.FiniteEndpointMetadata30Data.naturalRow nwords 640 start_index 40768 row_count 64

theorem chunk_637 (i : Fin 64) (hi : 40768+i.val < 40920) :
    xorSum ((FiniteEndpointMetadata30Data.naturalRow (40768+i.val)).map
      FiniteEndpointInverse30.binaryInverse) = 2^(40768+i.val) := by
  fin_cases i
  · exact certificate.row_40768
  · exact certificate.row_40769
  · exact certificate.row_40770
  · exact certificate.row_40771
  · exact certificate.row_40772
  · exact certificate.row_40773
  · exact certificate.row_40774
  · exact certificate.row_40775
  · exact certificate.row_40776
  · exact certificate.row_40777
  · exact certificate.row_40778
  · exact certificate.row_40779
  · exact certificate.row_40780
  · exact certificate.row_40781
  · exact certificate.row_40782
  · exact certificate.row_40783
  · exact certificate.row_40784
  · exact certificate.row_40785
  · exact certificate.row_40786
  · exact certificate.row_40787
  · exact certificate.row_40788
  · exact certificate.row_40789
  · exact certificate.row_40790
  · exact certificate.row_40791
  · exact certificate.row_40792
  · exact certificate.row_40793
  · exact certificate.row_40794
  · exact certificate.row_40795
  · exact certificate.row_40796
  · exact certificate.row_40797
  · exact certificate.row_40798
  · exact certificate.row_40799
  · exact certificate.row_40800
  · exact certificate.row_40801
  · exact certificate.row_40802
  · exact certificate.row_40803
  · exact certificate.row_40804
  · exact certificate.row_40805
  · exact certificate.row_40806
  · exact certificate.row_40807
  · exact certificate.row_40808
  · exact certificate.row_40809
  · exact certificate.row_40810
  · exact certificate.row_40811
  · exact certificate.row_40812
  · exact certificate.row_40813
  · exact certificate.row_40814
  · exact certificate.row_40815
  · exact certificate.row_40816
  · exact certificate.row_40817
  · exact certificate.row_40818
  · exact certificate.row_40819
  · exact certificate.row_40820
  · exact certificate.row_40821
  · exact certificate.row_40822
  · exact certificate.row_40823
  · exact certificate.row_40824
  · exact certificate.row_40825
  · exact certificate.row_40826
  · exact certificate.row_40827
  · exact certificate.row_40828
  · exact certificate.row_40829
  · exact certificate.row_40830
  · exact certificate.row_40831

certify_sparse_rows certificate from "certificates/finite/n30/sparse.bin" inverse_file "certificates/finite/n30/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse30.binaryInverse row_fn Quartic.FiniteEndpointMetadata30Data.naturalRow nwords 640 start_index 40832 row_count 64

theorem chunk_638 (i : Fin 64) (hi : 40832+i.val < 40920) :
    xorSum ((FiniteEndpointMetadata30Data.naturalRow (40832+i.val)).map
      FiniteEndpointInverse30.binaryInverse) = 2^(40832+i.val) := by
  fin_cases i
  · exact certificate.row_40832
  · exact certificate.row_40833
  · exact certificate.row_40834
  · exact certificate.row_40835
  · exact certificate.row_40836
  · exact certificate.row_40837
  · exact certificate.row_40838
  · exact certificate.row_40839
  · exact certificate.row_40840
  · exact certificate.row_40841
  · exact certificate.row_40842
  · exact certificate.row_40843
  · exact certificate.row_40844
  · exact certificate.row_40845
  · exact certificate.row_40846
  · exact certificate.row_40847
  · exact certificate.row_40848
  · exact certificate.row_40849
  · exact certificate.row_40850
  · exact certificate.row_40851
  · exact certificate.row_40852
  · exact certificate.row_40853
  · exact certificate.row_40854
  · exact certificate.row_40855
  · exact certificate.row_40856
  · exact certificate.row_40857
  · exact certificate.row_40858
  · exact certificate.row_40859
  · exact certificate.row_40860
  · exact certificate.row_40861
  · exact certificate.row_40862
  · exact certificate.row_40863
  · exact certificate.row_40864
  · exact certificate.row_40865
  · exact certificate.row_40866
  · exact certificate.row_40867
  · exact certificate.row_40868
  · exact certificate.row_40869
  · exact certificate.row_40870
  · exact certificate.row_40871
  · exact certificate.row_40872
  · exact certificate.row_40873
  · exact certificate.row_40874
  · exact certificate.row_40875
  · exact certificate.row_40876
  · exact certificate.row_40877
  · exact certificate.row_40878
  · exact certificate.row_40879
  · exact certificate.row_40880
  · exact certificate.row_40881
  · exact certificate.row_40882
  · exact certificate.row_40883
  · exact certificate.row_40884
  · exact certificate.row_40885
  · exact certificate.row_40886
  · exact certificate.row_40887
  · exact certificate.row_40888
  · exact certificate.row_40889
  · exact certificate.row_40890
  · exact certificate.row_40891
  · exact certificate.row_40892
  · exact certificate.row_40893
  · exact certificate.row_40894
  · exact certificate.row_40895

certify_sparse_rows certificate from "certificates/finite/n30/sparse.bin" inverse_file "certificates/finite/n30/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse30.binaryInverse row_fn Quartic.FiniteEndpointMetadata30Data.naturalRow nwords 640 start_index 40896 row_count 24

theorem chunk_639 (i : Fin 64) (hi : 40896+i.val < 40920) :
    xorSum ((FiniteEndpointMetadata30Data.naturalRow (40896+i.val)).map
      FiniteEndpointInverse30.binaryInverse) = 2^(40896+i.val) := by
  fin_cases i
  · exact certificate.row_40896
  · exact certificate.row_40897
  · exact certificate.row_40898
  · exact certificate.row_40899
  · exact certificate.row_40900
  · exact certificate.row_40901
  · exact certificate.row_40902
  · exact certificate.row_40903
  · exact certificate.row_40904
  · exact certificate.row_40905
  · exact certificate.row_40906
  · exact certificate.row_40907
  · exact certificate.row_40908
  · exact certificate.row_40909
  · exact certificate.row_40910
  · exact certificate.row_40911
  · exact certificate.row_40912
  · exact certificate.row_40913
  · exact certificate.row_40914
  · exact certificate.row_40915
  · exact certificate.row_40916
  · exact certificate.row_40917
  · exact certificate.row_40918
  · exact certificate.row_40919
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

end Quartic.FiniteEndpointRows30
