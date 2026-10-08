import Quartic.ConvolutionLayerInclusions
import Quartic.ConvolutionCoreImages

/-!
# Layer subspaces inside actual quadratic multiplication images

The source is an actual direct sum of a core subspace and output subspaces
at individual free variables. All image inclusions below use polynomial
multipliers and the checked coordinate identities.
-/

noncomputable section
namespace Quartic.ConvolutionProfileImage
open MvPolynomial FreeCoefficients FreeMonomialCounts ConvolutionFreePieces
open ConvolutionFreeMultiplication ConvolutionLayers FreeCoefficientProducts
open ConvolutionLayerInclusions ConvolutionCoreImages
variable {K : Type*} [Field K] {t w : ℕ}

/-- Actual multiplication of a first-piece subspace by all homogeneous quadratics. -/
def quadraticImage (L : Submodule K (Piece K t w 1)) : Submodule K (Piece K t w 3) :=
  ⨆ f : Forms K (t + w) 2, L.map (pieceMul (t := t) (w := w) (d := 1) f)

theorem quadratic_multiple_mem (L : Submodule K (Piece K t w 1))
    (f : Forms K (t + w) 2) (x : Piece K t w 1) (hx : x ∈ L) :
    pieceMul f x ∈ quadraticImage L :=
  Submodule.mem_iSup_of_mem f ⟨x, hx, rfl⟩

/-- The subspace with the given core part and free output parts. -/
def splitSource (L : Submodule K (Piece K t 0 1)) (D : Fin w → Submodule K (Piece K t 0 0)) :
    Submodule K (Piece K t w 1) :=
  (L.prod (Submodule.pi Set.univ D)).map degreeOneEquiv.symm.toLinearMap

theorem mem_splitSource (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) (x : Piece K t w 1) :
    x ∈ splitSource L D ↔ (degreeOneEquiv x).1 ∈ L ∧ ∀ i, (degreeOneEquiv x).2 i ∈ D i := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    change v.1 ∈ L ∧ v.2 ∈ Submodule.pi Set.univ D at hv
    simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
      (⟨hv.1, fun i => hv.2 i (Set.mem_univ i)⟩ : v.1 ∈ L ∧ ∀ i, v.2 i ∈ D i)
  · intro hx
    refine ⟨degreeOneEquiv x, ?_, degreeOneEquiv.symm_apply_apply x⟩
    exact ⟨hx.1, fun i _ => hx.2 i⟩

theorem insert_core_mem (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) (x : Piece K t 0 1) (hx : x ∈ L) :
    insertAt (zeroExponent w) x ∈ splitSource L D := by
  rw [mem_splitSource, degreeOne_insert_core]
  exact ⟨hx, fun i => (D i).zero_mem⟩

theorem insert_free_mem (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) (i : Fin w) (x : Piece K t 0 0)
    (hx : x ∈ D i) : insertAt (oneExponentEquiv i) x ∈ splitSource L D := by
  classical
  rw [mem_splitSource, degreeOne_insert_free]
  refine ⟨L.zero_mem, ?_⟩
  intro j
  by_cases h : i = j
  · subst j
    simpa using hx
  · simp [h]

/-- Every free quadratic gives an independent placed copy of the core source in the image. -/
theorem core_free_quadratic_mem (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) (b : ExactExponent w 2)
    (x : Piece K t 0 1) (hx : x ∈ L) :
    insertAt b x ∈ quadraticImage (splitSource L D) := by
  have h := quadratic_multiple_mem (splitSource L D) (freeFormAt b)
    (insertAt (zeroExponent w) x) (insert_core_mem L D x hx)
  rw [insertAt_free_product (d := 1) b (zeroExponent w) x] at h
  simpa only [addExponent_zero, pieceCast_self] using h

/-- Multiplying the core source by a core linear form and one free variable gives its
actual first-layer core-linear image. -/
theorem core_linear_free_mem (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) (i : Fin w) (f : Forms K t 1)
    (x : Piece K t 0 1) (hx : x ∈ L) :
    insertAt (oneExponentEquiv i) (pieceMul (w := 0) f x) ∈
      quadraticImage (splitSource L D) := by
  have h := quadratic_multiple_mem (splitSource L D) (formAt (oneExponentEquiv i) f)
    (insertAt (zeroExponent w) x) (insert_core_mem L D x hx)
  rw [insertAt_product (d := 1) (oneExponentEquiv i) (zeroExponent w) f x] at h
  simpa only [addExponent_zero, pieceCast_self] using h

/-- The whole coordinate-variable core image embeds into each linear free layer. -/
theorem coreLinearImage_mem (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) (i : Fin w) :
    coreLinearImage L ≤ (quadraticImage (splitSource L D)).comap (insertAt (oneExponentEquiv i)) := by
  apply iSup_le
  intro j
  rintro _ ⟨x, hx, rfl⟩
  exact core_linear_free_mem L D i _ x hx

/-- Quadratic multiplication of an incident output class fills the corresponding core layer. -/
theorem output_quadratic_free_mem (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) (i : Fin w) (f : Forms K t 2)
    (x : Piece K t 0 0) (hx : x ∈ D i) :
    insertAt (oneExponentEquiv i) (outputMul f x) ∈ quadraticImage (splitSource L D) := by
  have h := quadratic_multiple_mem (splitSource L D) (formAt (zeroExponent w) f)
    (insertAt (oneExponentEquiv i) x) (insert_free_mem L D i x hx)
  have he : addExponent (zeroExponent w) (oneExponentEquiv i) = oneExponentEquiv i := by
    apply Subtype.ext
    simp [addExponent, zeroExponent]
  rw [insertAt_product (d := 0) (zeroExponent w) (oneExponentEquiv i) f x] at h
  simpa only [pieceCast_self, he, outputMul, pieceDegreeEquiv, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.refl_apply] using h

theorem outputQuadraticImage_mem (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) (i : Fin w) :
    outputImage 2 (D i) ≤
      (quadraticImage (splitSource L D)).comap (insertAt (oneExponentEquiv i)) := by
  apply iSup_le
  intro f
  rintro _ ⟨x, hx, rfl⟩
  exact output_quadratic_free_mem L D i f x hx

/-- Remove one occurrence of an incident free variable from a monomial. -/
def removeVariable {k : ℕ} (b : ExactExponent w (k + 1)) (i : Fin w) (hi : 0 < b.val i) :
    ExactExponent w k :=
  ⟨b.val - Finsupp.single i 1, by
    have h := tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (by omega : 1 ≤ b.val i))
    have hd := congrArg Finsupp.degree h
    rw [map_add, Finsupp.degree_single, b.property] at hd
    omega⟩

theorem removeVariable_add {k : ℕ} (b : ExactExponent w (k + 1)) (i : Fin w)
    (hi : 0 < b.val i) : addExponent (removeVariable b i hi) (oneExponentEquiv i) = b := by
  apply Subtype.ext
  change b.val - Finsupp.single i 1 + (oneExponentEquiv i).val = b.val
  rw [oneExponentEquiv_val]
  exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (by omega))

/-- An incident output linear product appears at every quadratic free monomial containing it. -/
theorem output_linear_quadratic_mem (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) (b : ExactExponent w 2) (i : Fin w)
    (hi : 0 < b.val i) (f : Forms K t 1) (x : Piece K t 0 0) (hx : x ∈ D i) :
    insertAt b (outputMul f x) ∈ quadraticImage (splitSource L D) := by
  have h := quadratic_multiple_mem (splitSource L D) (formAt (removeVariable (k := 1) b i hi) f)
    (insertAt (oneExponentEquiv i) x) (insert_free_mem L D i x hx)
  rw [insertAt_product (d := 0) (removeVariable (k := 1) b i hi) (oneExponentEquiv i) f x] at h
  simpa only [pieceCast_self, removeVariable_add, outputMul, pieceDegreeEquiv, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.refl_apply] using h

theorem outputLinearImage_mem (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) (b : ExactExponent w 2) (i : Fin w)
    (hi : 0 < b.val i) :
    outputImage 1 (D i) ≤ (quadraticImage (splitSource L D)).comap (insertAt b) := by
  apply iSup_le
  intro f
  rintro _ ⟨x, hx, rfl⟩
  exact output_linear_quadratic_mem L D b i hi f x hx

/-- An incident output class appears at every cubic free monomial containing its variable. -/
theorem output_cubic_mem (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) (b : ExactExponent w 3) (i : Fin w)
    (hi : 0 < b.val i) (x : Piece K t 0 0) (hx : x ∈ D i) :
    insertAt b x ∈ quadraticImage (splitSource L D) := by
  have h := quadratic_multiple_mem (splitSource L D) (freeFormAt (removeVariable (k := 2) b i hi))
    (insertAt (oneExponentEquiv i) x) (insert_free_mem L D i x hx)
  rw [insertAt_free_product (d := 0) (removeVariable (k := 2) b i hi) (oneExponentEquiv i) x] at h
  simpa only [pieceCast_self, removeVariable_add] using h

/-- The two guaranteed subspaces in each linear free layer. -/
def linearLayer (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) (i : Fin w) : Submodule K (Piece K t 0 2) :=
  coreLinearImage L ⊔ outputImage 2 (D i)

/-- The guaranteed core-linear subspaces at an actual quadratic free monomial. -/
def quadraticLayer (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) (b : ExactExponent w 2) :
    Submodule K (Piece K t 0 1) :=
  L ⊔ ⨆ i : {i : Fin w // 0 < b.val i}, outputImage 1 (D i.val)

/-- The sum of the incident output subspaces at an actual cubic free monomial. -/
def cubicLayer (D : Fin w → Submodule K (Piece K t 0 0)) (b : ExactExponent w 3) :
    Submodule K (Piece K t 0 0) :=
  ⨆ i : {i : Fin w // 0 < b.val i}, D i.val

theorem linearLayer_mem (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) (i : Fin w) :
    linearLayer L D i ≤
      (quadraticImage (splitSource L D)).comap (insertAt (oneExponentEquiv i)) :=
  sup_le (coreLinearImage_mem L D i) (outputQuadraticImage_mem L D i)

theorem quadraticLayer_mem (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) (b : ExactExponent w 2) :
    quadraticLayer L D b ≤ (quadraticImage (splitSource L D)).comap (insertAt b) := by
  apply sup_le
  · exact fun x hx => core_free_quadratic_mem L D b x hx
  · apply iSup_le
    intro i
    exact outputLinearImage_mem L D b i.val i.property

theorem cubicLayer_mem (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) (b : ExactExponent w 3) :
    cubicLayer D b ≤ (quadraticImage (splitSource L D)).comap (insertAt b) := by
  apply iSup_le
  intro i
  exact fun x hx => output_cubic_mem L D b i.val i.property x hx

end Quartic.ConvolutionProfileImage
