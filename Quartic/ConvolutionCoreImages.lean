import Quartic.ConvolutionFreeMultiplication
import Quartic.ConvolutionShadow
import Quartic.ConvolutionOutputLinear

/-!
# Core multiplication bounds in the free-piece quotient model

The canonical quotient identifications intertwine actual polynomial
multiplication on `Piece` with the previously checked core multiplication and
output maps. All image dimensions below are transported through these explicit
map identities, with no assumed rank equalities.
-/

noncomputable section
namespace Quartic.ConvolutionCoreImages
open MvPolynomial ConvolutionPresentation ConvolutionFreePieces ConvolutionFreeMultiplication
open ConvolutionEvaluation ConvolutionOutput ConvolutionOutputLinear
variable {K : Type*} [Field K] {t : ℕ}

abbrev coreZeroEquiv : Piece K t 0 0 ≃ₗ[K] DegreeZero K t := pieceZeroEquiv
abbrev coreOneEquiv : Piece K t 0 1 ≃ₗ[K] Cokernel K t 0 := corePieceSuccEquiv
abbrev coreTwoEquiv : Piece K t 0 2 ≃ₗ[K] Cokernel K t 1 := corePieceSuccEquiv

@[simp] theorem coreZeroEquiv_mk (v : Target K t 0) :
    coreZeroEquiv (Submodule.Quotient.mk v) = v := by
  simp [coreZeroEquiv, pieceZeroEquiv]

@[simp] theorem coreOneEquiv_mk (v : Target K t 1) :
    coreOneEquiv (Submodule.Quotient.mk v) = (Submodule.Quotient.mk v : Cokernel K t 0) := rfl

@[simp] theorem coreTwoEquiv_mk (v : Target K t 2) :
    coreTwoEquiv (Submodule.Quotient.mk v) = (Submodule.Quotient.mk v : Cokernel K t 1) := rfl

/-- The new and old quotient multiplications agree on every core class. -/
theorem coreOne_mul_compat (f : Forms K t 1) (x : Piece K t 0 1) :
    coreTwoEquiv (pieceMul f x) =
      ConvolutionMultiplication.quotientMul f (coreOneEquiv x) := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  rw [pieceMul_mk, coreTwoEquiv_mk, coreOneEquiv_mk,
    ConvolutionMultiplication.quotientMul_mk]
  rfl

/-- Multiplication of a core degree-one subspace by the coordinate variables. -/
def coreLinearImage (L : Submodule K (Piece K t 0 1)) : Submodule K (Piece K t 0 2) :=
  ⨆ i : Fin t, L.map (pieceMul (t := t) (w := 0) (d := 1) (variableForm i))

/-- Canonical quotient transport identifies the complete coordinate-variable images. -/
theorem map_coreLinearImage (L : Submodule K (Piece K t 0 1)) :
    (coreLinearImage L).map coreTwoEquiv.toLinearMap =
      ConvolutionImage.imageSpace (L.map coreOneEquiv.toLinearMap) := by
  rw [coreLinearImage, Submodule.map_iSup, ConvolutionImage.imageSpace]
  congr 1
  funext i
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact coreOne_mul_compat (variableForm i) x

/-- The sharp core linear-image estimate, now on the actual `Piece` model. -/
theorem coreLinearImage_sharp_bound [Infinite K] (ht : 2 ≤ t)
    (L : Submodule K (Piece K t 0 1)) :
    t.choose 2 - (t - (Module.finrank K L + 1) / 2).choose 2 ≤
      Module.finrank K (coreLinearImage L) := by
  have h := ConvolutionShadow.sharp_linear_image_bound ht (L.map coreOneEquiv.toLinearMap)
  rw [coreOneEquiv.finrank_map_eq L, ← map_coreLinearImage, coreTwoEquiv.finrank_map_eq] at h
  exact h

/-- The linear relaxation of the core bound, with denominators cleared. -/
theorem coreLinearImage_linear_bound [Infinite K] (ht : 2 ≤ t)
    (L : Submodule K (Piece K t 0 1)) :
    t * Module.finrank K L ≤ 4 * Module.finrank K (coreLinearImage L) := by
  have h := ConvolutionShadow.linear_image_bound ht (L.map coreOneEquiv.toLinearMap)
  rw [coreOneEquiv.finrank_map_eq L, ← map_coreLinearImage, coreTwoEquiv.finrank_map_eq] at h
  exact h

/-- Transport a core piece across an equality of its homogeneous degree. -/
def pieceDegreeEquiv {d e : ℕ} (h : d = e) : Piece K t 0 d ≃ₗ[K] Piece K t 0 e := by
  subst e
  exact LinearEquiv.refl K _

/-- Multiply a degree-zero core class by an arbitrary homogeneous polynomial. -/
def outputMul {k : ℕ} (f : Forms K t k) : Piece K t 0 0 →ₗ[K] Piece K t 0 k :=
  (pieceDegreeEquiv (Nat.zero_add k)).toLinearMap.comp (pieceMul (w := 0) (d := 0) f)

/-- The full output image under all forms of the requested degree. -/
def outputImage (k : ℕ) (D : Submodule K (Piece K t 0 0)) : Submodule K (Piece K t 0 k) :=
  ⨆ f : Forms K t k, D.map (outputMul f)

/-- Linear output multiplication agrees with its old model on representatives. -/
theorem outputMul_one_compat (f : Forms K t 1) (x : Piece K t 0 0) :
    coreOneEquiv (outputMul f x) = linearFromOutput (coreZeroEquiv x) f := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  change coreOneEquiv (pieceMul f (Submodule.Quotient.mk v)) = _
  rw [pieceMul_mk, coreOneEquiv_mk, coreZeroEquiv_mk]
  change (Submodule.Quotient.mk (rowMul f v) : Cokernel K t 0) =
    Submodule.Quotient.mk (outputTarget (outputCoefficients v) 1 f)
  congr 1
  funext r
  apply Subtype.ext
  rw [rowMul_apply_val, outputTarget_from_degreeZero_val]
  exact mul_comm _ _

/-- Quadratic output multiplication agrees with its old model on representatives. -/
theorem outputMul_two_compat (f : Forms K t 2) (x : Piece K t 0 0) :
    coreTwoEquiv (outputMul f x) = quadraticFromOutput (coreZeroEquiv x) f := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  change coreTwoEquiv (pieceMul f (Submodule.Quotient.mk v)) = _
  rw [pieceMul_mk, coreTwoEquiv_mk, coreZeroEquiv_mk]
  change (Submodule.Quotient.mk (rowMul f v) : Cokernel K t 1) =
    Submodule.Quotient.mk (outputTarget (outputCoefficients v) 2 f)
  congr 1
  funext r
  apply Subtype.ext
  rw [rowMul_apply_val, outputTarget_from_degreeZero_val]
  exact mul_comm _ _

section FamilyImage
variable {F V V' W W' : Type*}
  [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V'] [AddCommGroup W] [Module K W]
  [AddCommGroup W'] [Module K W']

/-- Intertwining product maps identifies their complete multiplication images. -/
theorem map_family_image (e : V ≃ₗ[K] V') (g : W ≃ₗ[K] W')
    (μ : F → (V →ₗ[K] W)) (ν : V' → (F →ₗ[K] W'))
    (h : ∀ f x, g (μ f x) = ν (e x) f) (D : Submodule K V) :
    (⨆ f : F, D.map (μ f)).map g.toLinearMap =
      ⨆ x : D.map e.toLinearMap, LinearMap.range (ν x.val) := by
  apply le_antisymm
  · rw [Submodule.map_iSup]
    apply iSup_le
    intro f
    rintro _ ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact (le_iSup (fun x : D.map e.toLinearMap => LinearMap.range (ν x.val))
      ⟨e x, ⟨x, hx, rfl⟩⟩) ⟨f, (h f x).symm⟩
  · apply iSup_le
    intro x
    rintro _ ⟨f, rfl⟩
    obtain ⟨v, hv, hev⟩ := x.property
    refine ⟨μ f v, (le_iSup (fun f : F => D.map (μ f)) f) ⟨v, hv, rfl⟩, ?_⟩
    change g (μ f v) = ν x.val f
    rw [h]
    change e v = x.val at hev
    rw [hev]

end FamilyImage

/-- The linear output image is identified with the previously proved actual output image. -/
theorem map_outputImage_one (D : Submodule K (Piece K t 0 0)) :
    (outputImage 1 D).map coreOneEquiv.toLinearMap =
      linearOutputImage (D.map coreZeroEquiv.toLinearMap) :=
  map_family_image coreZeroEquiv coreOneEquiv outputMul linearFromOutput outputMul_one_compat D

/-- The quadratic output image is identified with the previously proved actual output image. -/
theorem map_outputImage_two (D : Submodule K (Piece K t 0 0)) :
    (outputImage 2 D).map coreTwoEquiv.toLinearMap =
      quadraticOutputImage (D.map coreZeroEquiv.toLinearMap) :=
  map_family_image coreZeroEquiv coreTwoEquiv outputMul quadraticFromOutput outputMul_two_compat D

/-- Uniform linear output-image bound in the actual core-piece coordinates. -/
theorem outputImage_one_bound (ht : 2 ≤ t) (D : Submodule K (Piece K t 0 0)) :
    min (Module.finrank K D) 2 * (t - 1) ≤ Module.finrank K (outputImage 1 D) := by
  have h := output_linear_finrank_bound ht (D.map coreZeroEquiv.toLinearMap)
  rw [coreZeroEquiv.finrank_map_eq D, ← map_outputImage_one, coreOneEquiv.finrank_map_eq] at h
  exact h

/-- Every nonzero output subspace generates the full actual degree-two core piece. -/
theorem outputImage_two_eq_top {D : Submodule K (Piece K t 0 0)} (hD : D ≠ ⊥) :
    outputImage 2 D = ⊤ := by
  have hmap : D.map coreZeroEquiv.toLinearMap ≠ ⊥ := by
    obtain ⟨x, hx, hne⟩ := D.ne_bot_iff.mp hD
    intro hzero
    have hx' : coreZeroEquiv x ∈ D.map coreZeroEquiv.toLinearMap := ⟨x, hx, rfl⟩
    rw [hzero] at hx'
    have hz : coreZeroEquiv x = 0 := hx'
    apply hne
    exact coreZeroEquiv.injective (hz.trans coreZeroEquiv.map_zero.symm)
  have h := quadraticOutputImage_eq_top hmap
  rw [← map_outputImage_two] at h
  apply (Submodule.map_injective_of_injective coreTwoEquiv.injective)
  simpa using h

end Quartic.ConvolutionCoreImages
