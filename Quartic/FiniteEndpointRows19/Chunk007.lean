import Quartic.FiniteEndpointInverseMemo19
import Quartic.FiniteEndpointMetadata19Data

/-! Kernel-checked rows of the actual quartic multiplication matrix. -/
namespace Quartic.FiniteEndpointRows19
open FiniteEndpointChecker
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 64000000

certify_sparse_rows certificate from "certificates/finite/n19/sparse.bin" inverse_file "certificates/finite/n19/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse19.binaryInverse row_fn Quartic.FiniteEndpointMetadata19Data.naturalRow nwords 115 start_index 7168 row_count 64

theorem chunk_112 (i : Fin 64) (hi : 7168+i.val < 7315) :
    xorSum ((FiniteEndpointMetadata19Data.naturalRow (7168+i.val)).map
      FiniteEndpointInverse19.binaryInverse) = 2^(7168+i.val) := by
  fin_cases i
  · exact certificate.row_7168
  · exact certificate.row_7169
  · exact certificate.row_7170
  · exact certificate.row_7171
  · exact certificate.row_7172
  · exact certificate.row_7173
  · exact certificate.row_7174
  · exact certificate.row_7175
  · exact certificate.row_7176
  · exact certificate.row_7177
  · exact certificate.row_7178
  · exact certificate.row_7179
  · exact certificate.row_7180
  · exact certificate.row_7181
  · exact certificate.row_7182
  · exact certificate.row_7183
  · exact certificate.row_7184
  · exact certificate.row_7185
  · exact certificate.row_7186
  · exact certificate.row_7187
  · exact certificate.row_7188
  · exact certificate.row_7189
  · exact certificate.row_7190
  · exact certificate.row_7191
  · exact certificate.row_7192
  · exact certificate.row_7193
  · exact certificate.row_7194
  · exact certificate.row_7195
  · exact certificate.row_7196
  · exact certificate.row_7197
  · exact certificate.row_7198
  · exact certificate.row_7199
  · exact certificate.row_7200
  · exact certificate.row_7201
  · exact certificate.row_7202
  · exact certificate.row_7203
  · exact certificate.row_7204
  · exact certificate.row_7205
  · exact certificate.row_7206
  · exact certificate.row_7207
  · exact certificate.row_7208
  · exact certificate.row_7209
  · exact certificate.row_7210
  · exact certificate.row_7211
  · exact certificate.row_7212
  · exact certificate.row_7213
  · exact certificate.row_7214
  · exact certificate.row_7215
  · exact certificate.row_7216
  · exact certificate.row_7217
  · exact certificate.row_7218
  · exact certificate.row_7219
  · exact certificate.row_7220
  · exact certificate.row_7221
  · exact certificate.row_7222
  · exact certificate.row_7223
  · exact certificate.row_7224
  · exact certificate.row_7225
  · exact certificate.row_7226
  · exact certificate.row_7227
  · exact certificate.row_7228
  · exact certificate.row_7229
  · exact certificate.row_7230
  · exact certificate.row_7231

certify_sparse_rows certificate from "certificates/finite/n19/sparse.bin" inverse_file "certificates/finite/n19/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse19.binaryInverse row_fn Quartic.FiniteEndpointMetadata19Data.naturalRow nwords 115 start_index 7232 row_count 64

theorem chunk_113 (i : Fin 64) (hi : 7232+i.val < 7315) :
    xorSum ((FiniteEndpointMetadata19Data.naturalRow (7232+i.val)).map
      FiniteEndpointInverse19.binaryInverse) = 2^(7232+i.val) := by
  fin_cases i
  · exact certificate.row_7232
  · exact certificate.row_7233
  · exact certificate.row_7234
  · exact certificate.row_7235
  · exact certificate.row_7236
  · exact certificate.row_7237
  · exact certificate.row_7238
  · exact certificate.row_7239
  · exact certificate.row_7240
  · exact certificate.row_7241
  · exact certificate.row_7242
  · exact certificate.row_7243
  · exact certificate.row_7244
  · exact certificate.row_7245
  · exact certificate.row_7246
  · exact certificate.row_7247
  · exact certificate.row_7248
  · exact certificate.row_7249
  · exact certificate.row_7250
  · exact certificate.row_7251
  · exact certificate.row_7252
  · exact certificate.row_7253
  · exact certificate.row_7254
  · exact certificate.row_7255
  · exact certificate.row_7256
  · exact certificate.row_7257
  · exact certificate.row_7258
  · exact certificate.row_7259
  · exact certificate.row_7260
  · exact certificate.row_7261
  · exact certificate.row_7262
  · exact certificate.row_7263
  · exact certificate.row_7264
  · exact certificate.row_7265
  · exact certificate.row_7266
  · exact certificate.row_7267
  · exact certificate.row_7268
  · exact certificate.row_7269
  · exact certificate.row_7270
  · exact certificate.row_7271
  · exact certificate.row_7272
  · exact certificate.row_7273
  · exact certificate.row_7274
  · exact certificate.row_7275
  · exact certificate.row_7276
  · exact certificate.row_7277
  · exact certificate.row_7278
  · exact certificate.row_7279
  · exact certificate.row_7280
  · exact certificate.row_7281
  · exact certificate.row_7282
  · exact certificate.row_7283
  · exact certificate.row_7284
  · exact certificate.row_7285
  · exact certificate.row_7286
  · exact certificate.row_7287
  · exact certificate.row_7288
  · exact certificate.row_7289
  · exact certificate.row_7290
  · exact certificate.row_7291
  · exact certificate.row_7292
  · exact certificate.row_7293
  · exact certificate.row_7294
  · exact certificate.row_7295

certify_sparse_rows certificate from "certificates/finite/n19/sparse.bin" inverse_file "certificates/finite/n19/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse19.binaryInverse row_fn Quartic.FiniteEndpointMetadata19Data.naturalRow nwords 115 start_index 7296 row_count 19

theorem chunk_114 (i : Fin 64) (hi : 7296+i.val < 7315) :
    xorSum ((FiniteEndpointMetadata19Data.naturalRow (7296+i.val)).map
      FiniteEndpointInverse19.binaryInverse) = 2^(7296+i.val) := by
  fin_cases i
  · exact certificate.row_7296
  · exact certificate.row_7297
  · exact certificate.row_7298
  · exact certificate.row_7299
  · exact certificate.row_7300
  · exact certificate.row_7301
  · exact certificate.row_7302
  · exact certificate.row_7303
  · exact certificate.row_7304
  · exact certificate.row_7305
  · exact certificate.row_7306
  · exact certificate.row_7307
  · exact certificate.row_7308
  · exact certificate.row_7309
  · exact certificate.row_7310
  · exact certificate.row_7311
  · exact certificate.row_7312
  · exact certificate.row_7313
  · exact certificate.row_7314
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

end Quartic.FiniteEndpointRows19
