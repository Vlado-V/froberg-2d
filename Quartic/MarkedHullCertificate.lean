module

public import Quartic.MarkedHullCertificateData

@[expose] public section

/-! Marked lower-endpoint weak-vertex bounds for dimensions 130 through 319. -/

namespace Quartic.MarkedHullCertificate

open Quartic.Counts Quartic.FiniteCounts Quartic.ProfileCertificate Quartic.HullCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem all_configurations_verified (index : Fin 190) :
    let m := (index : ℕ) + 130
    ConfigurationBounds m (upperEndpoint m) (mixedCount m false) := by
  fin_cases index
  · exact configuration_130_lower
  · exact configuration_131_lower
  · exact configuration_132_lower
  · exact configuration_133_lower
  · exact configuration_134_lower
  · exact configuration_135_lower
  · exact configuration_136_lower
  · exact configuration_137_lower
  · exact configuration_138_lower
  · exact configuration_139_lower
  · exact configuration_140_lower
  · exact configuration_141_lower
  · exact configuration_142_lower
  · exact configuration_143_lower
  · exact configuration_144_lower
  · exact configuration_145_lower
  · exact configuration_146_lower
  · exact configuration_147_lower
  · exact configuration_148_lower
  · exact configuration_149_lower
  · exact configuration_150_lower
  · exact configuration_151_lower
  · exact configuration_152_lower
  · exact configuration_153_lower
  · exact configuration_154_lower
  · exact configuration_155_lower
  · exact configuration_156_lower
  · exact configuration_157_lower
  · exact configuration_158_lower
  · exact configuration_159_lower
  · exact configuration_160_lower
  · exact configuration_161_lower
  · exact configuration_162_lower
  · exact configuration_163_lower
  · exact configuration_164_lower
  · exact configuration_165_lower
  · exact configuration_166_lower
  · exact configuration_167_lower
  · exact configuration_168_lower
  · exact configuration_169_lower
  · exact configuration_170_lower
  · exact configuration_171_lower
  · exact configuration_172_lower
  · exact configuration_173_lower
  · exact configuration_174_lower
  · exact configuration_175_lower
  · exact configuration_176_lower
  · exact configuration_177_lower
  · exact configuration_178_lower
  · exact configuration_179_lower
  · exact configuration_180_lower
  · exact configuration_181_lower
  · exact configuration_182_lower
  · exact configuration_183_lower
  · exact configuration_184_lower
  · exact configuration_185_lower
  · exact configuration_186_lower
  · exact configuration_187_lower
  · exact configuration_188_lower
  · exact configuration_189_lower
  · exact configuration_190_lower
  · exact configuration_191_lower
  · exact configuration_192_lower
  · exact configuration_193_lower
  · exact configuration_194_lower
  · exact configuration_195_lower
  · exact configuration_196_lower
  · exact configuration_197_lower
  · exact configuration_198_lower
  · exact configuration_199_lower
  · exact configuration_200_lower
  · exact configuration_201_lower
  · exact configuration_202_lower
  · exact configuration_203_lower
  · exact configuration_204_lower
  · exact configuration_205_lower
  · exact configuration_206_lower
  · exact configuration_207_lower
  · exact configuration_208_lower
  · exact configuration_209_lower
  · exact configuration_210_lower
  · exact configuration_211_lower
  · exact configuration_212_lower
  · exact configuration_213_lower
  · exact configuration_214_lower
  · exact configuration_215_lower
  · exact configuration_216_lower
  · exact configuration_217_lower
  · exact configuration_218_lower
  · exact configuration_219_lower
  · exact configuration_220_lower
  · exact configuration_221_lower
  · exact configuration_222_lower
  · exact configuration_223_lower
  · exact configuration_224_lower
  · exact configuration_225_lower
  · exact configuration_226_lower
  · exact configuration_227_lower
  · exact configuration_228_lower
  · exact configuration_229_lower
  · exact configuration_230_lower
  · exact configuration_231_lower
  · exact configuration_232_lower
  · exact configuration_233_lower
  · exact configuration_234_lower
  · exact configuration_235_lower
  · exact configuration_236_lower
  · exact configuration_237_lower
  · exact configuration_238_lower
  · exact configuration_239_lower
  · exact configuration_240_lower
  · exact configuration_241_lower
  · exact configuration_242_lower
  · exact configuration_243_lower
  · exact configuration_244_lower
  · exact configuration_245_lower
  · exact configuration_246_lower
  · exact configuration_247_lower
  · exact configuration_248_lower
  · exact configuration_249_lower
  · exact configuration_250_lower
  · exact configuration_251_lower
  · exact configuration_252_lower
  · exact configuration_253_lower
  · exact configuration_254_lower
  · exact configuration_255_lower
  · exact configuration_256_lower
  · exact configuration_257_lower
  · exact configuration_258_lower
  · exact configuration_259_lower
  · exact configuration_260_lower
  · exact configuration_261_lower
  · exact configuration_262_lower
  · exact configuration_263_lower
  · exact configuration_264_lower
  · exact configuration_265_lower
  · exact configuration_266_lower
  · exact configuration_267_lower
  · exact configuration_268_lower
  · exact configuration_269_lower
  · exact configuration_270_lower
  · exact configuration_271_lower
  · exact configuration_272_lower
  · exact configuration_273_lower
  · exact configuration_274_lower
  · exact configuration_275_lower
  · exact configuration_276_lower
  · exact configuration_277_lower
  · exact configuration_278_lower
  · exact configuration_279_lower
  · exact configuration_280_lower
  · exact configuration_281_lower
  · exact configuration_282_lower
  · exact configuration_283_lower
  · exact configuration_284_lower
  · exact configuration_285_lower
  · exact configuration_286_lower
  · exact configuration_287_lower
  · exact configuration_288_lower
  · exact configuration_289_lower
  · exact configuration_290_lower
  · exact configuration_291_lower
  · exact configuration_292_lower
  · exact configuration_293_lower
  · exact configuration_294_lower
  · exact configuration_295_lower
  · exact configuration_296_lower
  · exact configuration_297_lower
  · exact configuration_298_lower
  · exact configuration_299_lower
  · exact configuration_300_lower
  · exact configuration_301_lower
  · exact configuration_302_lower
  · exact configuration_303_lower
  · exact configuration_304_lower
  · exact configuration_305_lower
  · exact configuration_306_lower
  · exact configuration_307_lower
  · exact configuration_308_lower
  · exact configuration_309_lower
  · exact configuration_310_lower
  · exact configuration_311_lower
  · exact configuration_312_lower
  · exact configuration_313_lower
  · exact configuration_314_lower
  · exact configuration_315_lower
  · exact configuration_316_lower
  · exact configuration_317_lower
  · exact configuration_318_lower
  · exact configuration_319_lower

/-- Every feasible source dimension has a supporting line satisfying the
incidence bounds after one scalar coefficient has been marked. -/
theorem hull_inequality (m : ℕ) (hmlo : 130 ≤ m) (hmhi : m ≤ 319)
    (cell : Fin 4) (d : ℤ) (hd : Eligible m (mixedCount m false) cell d) :
    let q := upperEndpoint m
    let c := mixedCount m false
    ∃ left right : ℕ, LineValid m c cell left right ∧
      IncidenceBounds (markedScalars (scalars m q c))
        (lineBetween (vertex m c cell left) (vertex m c cell right)) d := by
  have hconfig := all_configurations_verified ⟨m - 130, by omega⟩
  have hm : m - 130 + 130 = m := by omega
  simp only [hm] at hconfig
  exact hconfig cell d hd

/-- The stronger marked bounds hold at each point of the weak-vertex hull. -/
theorem hull_point_inequalities (m : ℕ) (hmlo : 130 ≤ m) (hmhi : m ≤ 319)
    (cell : Fin 4) (d : ℤ) (hd : Eligible m (mixedCount m false) cell d)
    (image : ℚ) (hpoint : InVertexHull m (mixedCount m false) cell d image) :
    ImageBounds (markedScalars (scalars m (upperEndpoint m) (mixedCount m false)))
      image d := by
  obtain ⟨left, right, hline, hinc⟩ := hull_inequality m hmlo hmhi cell d hd
  exact hinc.mono (hline.supports_hull hpoint)

end Quartic.MarkedHullCertificate
