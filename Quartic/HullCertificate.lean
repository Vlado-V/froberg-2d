module

public import Quartic.HullCertificate.Data
public import Quartic.HullCertificate.Full

@[expose] public section

/-!
# Verified weak-vertex supporting bounds, dimensions 130 through 319

All 380 endpoint configurations and their four knot cells have kernel-checked
supporting-line certificates. The line coefficients come from the manuscript's
rational weak vertices. The result includes both incidence inequalities for
every nontrivial integral source dimension in each cell.

The conversion from these vertex bounds to a bound on geometric image dimension
requires the manuscript's concavity/degeneration argument; it is not assumed or
asserted by this finite arithmetic certificate.
-/

namespace Quartic.HullCertificate

open Quartic.Counts Quartic.FiniteCounts Quartic.ProfileCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- All 380 configurations, linked to the sign-certified endpoint table. -/
theorem all_configurations_verified (index : Fin 190) (upper : Bool) :
    let m := (index : ℕ) + 130
    ConfigurationBounds m (upperEndpoint m) (mixedCount m upper) := by
  fin_cases index <;> cases upper
  · exact configuration_130_lower
  · exact configuration_130_upper
  · exact configuration_131_lower
  · exact configuration_131_upper
  · exact configuration_132_lower
  · exact configuration_132_upper
  · exact configuration_133_lower
  · exact configuration_133_upper
  · exact configuration_134_lower
  · exact configuration_134_upper
  · exact configuration_135_lower
  · exact configuration_135_upper
  · exact configuration_136_lower
  · exact configuration_136_upper
  · exact configuration_137_lower
  · exact configuration_137_upper
  · exact configuration_138_lower
  · exact configuration_138_upper
  · exact configuration_139_lower
  · exact configuration_139_upper
  · exact configuration_140_lower
  · exact configuration_140_upper
  · exact configuration_141_lower
  · exact configuration_141_upper
  · exact configuration_142_lower
  · exact configuration_142_upper
  · exact configuration_143_lower
  · exact configuration_143_upper
  · exact configuration_144_lower
  · exact configuration_144_upper
  · exact configuration_145_lower
  · exact configuration_145_upper
  · exact configuration_146_lower
  · exact configuration_146_upper
  · exact configuration_147_lower
  · exact configuration_147_upper
  · exact configuration_148_lower
  · exact configuration_148_upper
  · exact configuration_149_lower
  · exact configuration_149_upper
  · exact configuration_150_lower
  · exact configuration_150_upper
  · exact configuration_151_lower
  · exact configuration_151_upper
  · exact configuration_152_lower
  · exact configuration_152_upper
  · exact configuration_153_lower
  · exact configuration_153_upper
  · exact configuration_154_lower
  · exact configuration_154_upper
  · exact configuration_155_lower
  · exact configuration_155_upper
  · exact configuration_156_lower
  · exact configuration_156_upper
  · exact configuration_157_lower
  · exact configuration_157_upper
  · exact configuration_158_lower
  · exact configuration_158_upper
  · exact configuration_159_lower
  · exact configuration_159_upper
  · exact configuration_160_lower
  · exact configuration_160_upper
  · exact configuration_161_lower
  · exact configuration_161_upper
  · exact configuration_162_lower
  · exact configuration_162_upper
  · exact configuration_163_lower
  · exact configuration_163_upper
  · exact configuration_164_lower
  · exact configuration_164_upper
  · exact configuration_165_lower
  · exact configuration_165_upper
  · exact configuration_166_lower
  · exact configuration_166_upper
  · exact configuration_167_lower
  · exact configuration_167_upper
  · exact configuration_168_lower
  · exact configuration_168_upper
  · exact configuration_169_lower
  · exact configuration_169_upper
  · exact configuration_170_lower
  · exact configuration_170_upper
  · exact configuration_171_lower
  · exact configuration_171_upper
  · exact configuration_172_lower
  · exact configuration_172_upper
  · exact configuration_173_lower
  · exact configuration_173_upper
  · exact configuration_174_lower
  · exact configuration_174_upper
  · exact configuration_175_lower
  · exact configuration_175_upper
  · exact configuration_176_lower
  · exact configuration_176_upper
  · exact configuration_177_lower
  · exact configuration_177_upper
  · exact configuration_178_lower
  · exact configuration_178_upper
  · exact configuration_179_lower
  · exact configuration_179_upper
  · exact configuration_180_lower
  · exact configuration_180_upper
  · exact configuration_181_lower
  · exact configuration_181_upper
  · exact configuration_182_lower
  · exact configuration_182_upper
  · exact configuration_183_lower
  · exact configuration_183_upper
  · exact configuration_184_lower
  · exact configuration_184_upper
  · exact configuration_185_lower
  · exact configuration_185_upper
  · exact configuration_186_lower
  · exact configuration_186_upper
  · exact configuration_187_lower
  · exact configuration_187_upper
  · exact configuration_188_lower
  · exact configuration_188_upper
  · exact configuration_189_lower
  · exact configuration_189_upper
  · exact configuration_190_lower
  · exact configuration_190_upper
  · exact configuration_191_lower
  · exact configuration_191_upper
  · exact configuration_192_lower
  · exact configuration_192_upper
  · exact configuration_193_lower
  · exact configuration_193_upper
  · exact configuration_194_lower
  · exact configuration_194_upper
  · exact configuration_195_lower
  · exact configuration_195_upper
  · exact configuration_196_lower
  · exact configuration_196_upper
  · exact configuration_197_lower
  · exact configuration_197_upper
  · exact configuration_198_lower
  · exact configuration_198_upper
  · exact configuration_199_lower
  · exact configuration_199_upper
  · exact configuration_200_lower
  · exact configuration_200_upper
  · exact configuration_201_lower
  · exact configuration_201_upper
  · exact configuration_202_lower
  · exact configuration_202_upper
  · exact configuration_203_lower
  · exact configuration_203_upper
  · exact configuration_204_lower
  · exact configuration_204_upper
  · exact configuration_205_lower
  · exact configuration_205_upper
  · exact configuration_206_lower
  · exact configuration_206_upper
  · exact configuration_207_lower
  · exact configuration_207_upper
  · exact configuration_208_lower
  · exact configuration_208_upper
  · exact configuration_209_lower
  · exact configuration_209_upper
  · exact configuration_210_lower
  · exact configuration_210_upper
  · exact configuration_211_lower
  · exact configuration_211_upper
  · exact configuration_212_lower
  · exact configuration_212_upper
  · exact configuration_213_lower
  · exact configuration_213_upper
  · exact configuration_214_lower
  · exact configuration_214_upper
  · exact configuration_215_lower
  · exact configuration_215_upper
  · exact configuration_216_lower
  · exact configuration_216_upper
  · exact configuration_217_lower
  · exact configuration_217_upper
  · exact configuration_218_lower
  · exact configuration_218_upper
  · exact configuration_219_lower
  · exact configuration_219_upper
  · exact configuration_220_lower
  · exact configuration_220_upper
  · exact configuration_221_lower
  · exact configuration_221_upper
  · exact configuration_222_lower
  · exact configuration_222_upper
  · exact configuration_223_lower
  · exact configuration_223_upper
  · exact configuration_224_lower
  · exact configuration_224_upper
  · exact configuration_225_lower
  · exact configuration_225_upper
  · exact configuration_226_lower
  · exact configuration_226_upper
  · exact configuration_227_lower
  · exact configuration_227_upper
  · exact configuration_228_lower
  · exact configuration_228_upper
  · exact configuration_229_lower
  · exact configuration_229_upper
  · exact configuration_230_lower
  · exact configuration_230_upper
  · exact configuration_231_lower
  · exact configuration_231_upper
  · exact configuration_232_lower
  · exact configuration_232_upper
  · exact configuration_233_lower
  · exact configuration_233_upper
  · exact configuration_234_lower
  · exact configuration_234_upper
  · exact configuration_235_lower
  · exact configuration_235_upper
  · exact configuration_236_lower
  · exact configuration_236_upper
  · exact configuration_237_lower
  · exact configuration_237_upper
  · exact configuration_238_lower
  · exact configuration_238_upper
  · exact configuration_239_lower
  · exact configuration_239_upper
  · exact configuration_240_lower
  · exact configuration_240_upper
  · exact configuration_241_lower
  · exact configuration_241_upper
  · exact configuration_242_lower
  · exact configuration_242_upper
  · exact configuration_243_lower
  · exact configuration_243_upper
  · exact configuration_244_lower
  · exact configuration_244_upper
  · exact configuration_245_lower
  · exact configuration_245_upper
  · exact configuration_246_lower
  · exact configuration_246_upper
  · exact configuration_247_lower
  · exact configuration_247_upper
  · exact configuration_248_lower
  · exact configuration_248_upper
  · exact configuration_249_lower
  · exact configuration_249_upper
  · exact configuration_250_lower
  · exact configuration_250_upper
  · exact configuration_251_lower
  · exact configuration_251_upper
  · exact configuration_252_lower
  · exact configuration_252_upper
  · exact configuration_253_lower
  · exact configuration_253_upper
  · exact configuration_254_lower
  · exact configuration_254_upper
  · exact configuration_255_lower
  · exact configuration_255_upper
  · exact configuration_256_lower
  · exact configuration_256_upper
  · exact configuration_257_lower
  · exact configuration_257_upper
  · exact configuration_258_lower
  · exact configuration_258_upper
  · exact configuration_259_lower
  · exact configuration_259_upper
  · exact configuration_260_lower
  · exact configuration_260_upper
  · exact configuration_261_lower
  · exact configuration_261_upper
  · exact configuration_262_lower
  · exact configuration_262_upper
  · exact configuration_263_lower
  · exact configuration_263_upper
  · exact configuration_264_lower
  · exact configuration_264_upper
  · exact configuration_265_lower
  · exact configuration_265_upper
  · exact configuration_266_lower
  · exact configuration_266_upper
  · exact configuration_267_lower
  · exact configuration_267_upper
  · exact configuration_268_lower
  · exact configuration_268_upper
  · exact configuration_269_lower
  · exact configuration_269_upper
  · exact configuration_270_lower
  · exact configuration_270_upper
  · exact configuration_271_lower
  · exact configuration_271_upper
  · exact configuration_272_lower
  · exact configuration_272_upper
  · exact configuration_273_lower
  · exact configuration_273_upper
  · exact configuration_274_lower
  · exact configuration_274_upper
  · exact configuration_275_lower
  · exact configuration_275_upper
  · exact configuration_276_lower
  · exact configuration_276_upper
  · exact configuration_277_lower
  · exact configuration_277_upper
  · exact configuration_278_lower
  · exact configuration_278_upper
  · exact configuration_279_lower
  · exact configuration_279_upper
  · exact configuration_280_lower
  · exact configuration_280_upper
  · exact configuration_281_lower
  · exact configuration_281_upper
  · exact configuration_282_lower
  · exact configuration_282_upper
  · exact configuration_283_lower
  · exact configuration_283_upper
  · exact configuration_284_lower
  · exact configuration_284_upper
  · exact configuration_285_lower
  · exact configuration_285_upper
  · exact configuration_286_lower
  · exact configuration_286_upper
  · exact configuration_287_lower
  · exact configuration_287_upper
  · exact configuration_288_lower
  · exact configuration_288_upper
  · exact configuration_289_lower
  · exact configuration_289_upper
  · exact configuration_290_lower
  · exact configuration_290_upper
  · exact configuration_291_lower
  · exact configuration_291_upper
  · exact configuration_292_lower
  · exact configuration_292_upper
  · exact configuration_293_lower
  · exact configuration_293_upper
  · exact configuration_294_lower
  · exact configuration_294_upper
  · exact configuration_295_lower
  · exact configuration_295_upper
  · exact configuration_296_lower
  · exact configuration_296_upper
  · exact configuration_297_lower
  · exact configuration_297_upper
  · exact configuration_298_lower
  · exact configuration_298_upper
  · exact configuration_299_lower
  · exact configuration_299_upper
  · exact configuration_300_lower
  · exact configuration_300_upper
  · exact configuration_301_lower
  · exact configuration_301_upper
  · exact configuration_302_lower
  · exact configuration_302_upper
  · exact configuration_303_lower
  · exact configuration_303_upper
  · exact configuration_304_lower
  · exact configuration_304_upper
  · exact configuration_305_lower
  · exact configuration_305_upper
  · exact configuration_306_lower
  · exact configuration_306_upper
  · exact configuration_307_lower
  · exact configuration_307_upper
  · exact configuration_308_lower
  · exact configuration_308_upper
  · exact configuration_309_lower
  · exact configuration_309_upper
  · exact configuration_310_lower
  · exact configuration_310_upper
  · exact configuration_311_lower
  · exact configuration_311_upper
  · exact configuration_312_lower
  · exact configuration_312_upper
  · exact configuration_313_lower
  · exact configuration_313_upper
  · exact configuration_314_lower
  · exact configuration_314_upper
  · exact configuration_315_lower
  · exact configuration_315_upper
  · exact configuration_316_lower
  · exact configuration_316_upper
  · exact configuration_317_lower
  · exact configuration_317_upper
  · exact configuration_318_lower
  · exact configuration_318_upper
  · exact configuration_319_lower
  · exact configuration_319_upper

/-- Readable finite-range form: every feasible nontrivial integer dimension has
an explicit affine supporting line satisfying both incidence tests. -/
theorem hull_inequality (m : ℕ) (hmlo : 130 ≤ m) (hmhi : m ≤ 319)
    (upper : Bool) (cell : Fin 4) (d : ℤ)
    (hd : Eligible m (mixedCount m upper) cell d) :
    let q := upperEndpoint m
    let c := mixedCount m upper
    ∃ left right : ℕ, LineValid m c cell left right ∧
      IncidenceBounds (scalars m q c)
        (lineBetween (vertex m c cell left) (vertex m c cell right)) d := by
  have hconfig := all_configurations_verified ⟨m - 130, by omega⟩ upper
  have hm : m - 130 + 130 = m := by omega
  simp only [hm] at hconfig
  exact hconfig cell d hd

/-- The original scalar incidence inequalities hold at every point of every
weak-vertex hull, for both endpoints throughout the certified finite range. -/
theorem hull_point_inequalities (m : ℕ) (hmlo : 130 ≤ m) (hmhi : m ≤ 319)
    (upper : Bool) (cell : Fin 4) (d : ℤ)
    (hd : Eligible m (mixedCount m upper) cell d) (image : ℚ)
    (hpoint : InVertexHull m (mixedCount m upper) cell d image) :
    ImageBounds (scalars m (upperEndpoint m) (mixedCount m upper)) image d := by
  obtain ⟨left, right, hline, hinc⟩ := hull_inequality m hmlo hmhi upper cell d hd
  exact hinc.mono (hline.supports_hull hpoint)

end Quartic.HullCertificate
