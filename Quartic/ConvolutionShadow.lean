import Quartic.ConvolutionImage
import Quartic.ConvolutionLinearFactor
import Quartic.ShadowArithmetic

/-!
# The sharp lower bound for the actual convolution multiplication image

The inverse-system, Hilbert, contraction, and symmetric-evaluation theorems
are applied to the actual image of every subspace of the first graded
convolution cokernel. The resulting bound has no inverse-system or dimension
hypotheses: only the field and parameter assumptions of the theorem remain.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Quartic.ConvolutionShadow
open MvPolynomial ConvolutionPresentation ConvolutionDual ConvolutionInverse ConvolutionHilbert
open ConvolutionEvaluation ConvolutionBilinear ConvolutionImage
open ConvolutionFactor ConvolutionSlots ConvolutionConstantSlot ConvolutionLinearFactor
variable {K : Type*} [Field K] {t : ℕ}

/-- Evaluation of the actual quadratic factor agrees with bilinear evaluation
on the rational normal curve. -/
theorem factor_curve_functional (ht : 2 ≤ t) (a : K) (φ : annihilator K t 1) :
    coefficientFunctional (t - 1) 0 (evaluateSecond a (inverseFactor φ)) =
      bilinearMap (quadraticFactorMap ht φ) (RationalCurve.point (t - 1) a) := by
  apply (Pi.basisFun K (Fin (t - 1))).ext
  intro i
  rw [Pi.basisFun_apply]
  change coefficientFunctional (t - 1) 0 (evaluateSecond a (inverseFactor φ))
      (Pi.single i 1) = _
  rw [coefficientFunctional_single, bilinearMap_curve_single]
  have hnone : (inverseFactor φ).degreeOf none = 0 := by
    have := (inverseFactor_bounds φ).1
    omega
  conv_lhs => rw [← rename_erase_of_degree_none_zero (inverseFactor φ) hnone,
    ConvolutionBilinear.evaluateSecond_rename]
  rw [quadraticFactorMap_val]
  have he : (Finsupp.single (0 : Fin 1) i.val).mapDomain Option.some = oneExponent 0 i.val := by
    ext o
    cases o with
    | none => simp [Finsupp.mapDomain_single]
    | some k => fin_cases k; simp [Finsupp.mapDomain_single]
  rw [← he, coeff_rename_mapDomain _ (Option.some_injective (Fin 1))]

/-- The pair coordinates of actual contraction are precisely the graph pairs
required by the proved symmetric-family bound. -/
theorem pairMap_curve (ht : 2 ≤ t) (a : K) (φ : annihilator K t 1) :
    pairMap (evaluatedContract a φ) =
      (bilinearMap (quadraticFactorMap ht φ) (RationalCurve.point (t - 1) a),
        a • bilinearMap (quadraticFactorMap ht φ) (RationalCurve.point (t - 1) a)) := by
  rw [pairMap_evaluatedContract, factor_curve_functional ht a φ]

/-- Pair coordinates on the actual first cokernel dual. -/
def pairCoordinates : Module.Dual K (Cokernel K t 0) →ₗ[K]
    Module.Dual K (Fin (t - 1) → K) × Module.Dual K (Fin (t - 1) → K) :=
  pairMap.comp (cokernelDualEquiv K t 0).toLinearMap

theorem pairCoordinates_injective (ht : 2 ≤ t) :
    Function.Injective (pairCoordinates (K := K) (t := t)) :=
  (pairMap_injective ht).comp (cokernelDualEquiv K t 0).injective

/-- The original subspace annihilator in the two-component coordinates. -/
def annihilatorPairs (L : Submodule K (Cokernel K t 0)) :=
  L.dualAnnihilator.map (pairCoordinates (K := K) (t := t))

theorem annihilatorPairs_finrank (ht : 2 ≤ t) (L : Submodule K (Cokernel K t 0)) :
    Module.finrank K (annihilatorPairs L) = Module.finrank K L.dualAnnihilator :=
  (Submodule.equivMapOfInjective pairCoordinates (pairCoordinates_injective ht)
    L.dualAnnihilator).finrank_eq.symm

/-- Every actual image-annihilator evaluation lies in the transported source annihilator. -/
theorem image_contraction_mem (ht : 2 ≤ t) (L : Submodule K (Cokernel K t 0))
    (φ : (imageSpace L).dualAnnihilator) (a : K) :
    (imageBilinearMap ht L φ (RationalCurve.point (t - 1) a),
      a • imageBilinearMap ht L φ (RationalCurve.point (t - 1) a)) ∈ annihilatorPairs L := by
  refine ⟨evaluatedDual a φ.val, evaluatedDual_mem L φ.val φ.property a, ?_⟩
  change pairMap (cokernelDualEquiv K t 0 (evaluatedDual a φ.val)) = _
  rw [evaluatedDual_cokernelDualEquiv, pairMap_curve ht]
  rfl

/-- The actual multiplication-image annihilator satisfies the sharp symmetric bound. -/
theorem image_annihilator_bound [Infinite K] (ht : 2 ≤ t)
    (L : Submodule K (Cokernel K t 0)) :
    Module.finrank K (imageSpace L).dualAnnihilator ≤
      (Module.finrank K L.dualAnnihilator / 2 + 1).choose 2 := by
  have h := ContractionBound.dimension_bound (K := K) (U := (imageSpace L).dualAnnihilator)
    (imageBilinearMap ht L)
    (imageBilinearMap_injective ht L) (imageBilinearMap_symmetric ht L)
    (annihilatorPairs L) (image_contraction_mem ht L)
  rwa [annihilatorPairs_finrank ht L] at h

/-- The manuscript's sharp lower shadow bound, now for every actual subspace
of the degree-one convolution cokernel and every `t≥2`. -/
theorem sharp_linear_image_bound [Infinite K] (ht : 2 ≤ t)
    (L : Submodule K (Cokernel K t 0)) :
    t.choose 2 - (t - (Module.finrank K L + 1) / 2).choose 2 ≤
      Module.finrank K (imageSpace L) := by
  have hbound := image_annihilator_bound ht L
  have hsource := source_annihilator_dimension ht L
  have himage := image_annihilator_dimension ht L
  have hfloor : Module.finrank K L.dualAnnihilator / 2 + 1 =
      t - (Module.finrank K L + 1) / 2 := by omega
  rw [hfloor] at hbound
  omega


/-- The linear relaxation `dim(UL) ≥ (t/4)dim(L)`, with denominators cleared. -/
theorem linear_image_bound [Infinite K] (ht : 2 ≤ t)
    (L : Submodule K (Cokernel K t 0)) :
    t * Module.finrank K L ≤ 4 * Module.finrank K (imageSpace L) := by
  have hsource := source_annihilator_dimension ht L
  have himage := image_annihilator_dimension ht L
  have hbound := image_annihilator_bound ht L
  have hi : Module.finrank K L ≤ 2 * (t - 1) := by omega
  have hlinear := ShadowArithmetic.shadow_linear_bound (t - 1) (Module.finrank K L) hi
  have hfloor : Module.finrank K L.dualAnnihilator / 2 + 1 =
      t - 1 - (Module.finrank K L + 1) / 2 + 1 := by omega
  rw [hfloor] at hbound
  have hgap : t.choose 2 ≤ Module.finrank K (imageSpace L) +
      (t - 1 - (Module.finrank K L + 1) / 2 + 1).choose 2 := by omega
  have hgap' : (t.choose 2 : ℤ) ≤ (Module.finrank K (imageSpace L) : ℤ) +
      ((t - 1 - (Module.finrank K L + 1) / 2 + 1).choose 2 : ℤ) := by exact_mod_cast hgap
  have htNat : t - 1 + 1 = t := by omega
  have htInt : ((t - 1 : ℕ) : ℤ) + 1 = t := by omega
  simp only [ShadowArithmetic.shadow, htNat, htInt] at hlinear
  have h : (t : ℤ) * (Module.finrank K L : ℤ) ≤
      4 * (Module.finrank K (imageSpace L) : ℤ) := by omega
  exact_mod_cast h

end Quartic.ConvolutionShadow
