import Quartic.ConvolutionInitialImage
import Quartic.ConvolutionProfileDimension

/-!
# Initial degree-one subspaces are split convolution sources

Independent free-coefficient blocks in degree one consist exactly of the core
block and one output block for each free variable. The initial replacement thus
has the split form used by the actual sharp-profile image theorem.
-/
noncomputable section
namespace Quartic.ConvolutionInitialSplit
open FreeCoefficients FreeMonomialCounts ConvolutionFreePieces ConvolutionLayers
open FreeCoefficientProducts ConvolutionLayerInclusions ConvolutionProfileImage
open ConvolutionInitialImage OrderedFreeExponents
variable {K : Type*} [Field K] {t w : ℕ}

/-- A full product of ordered coefficient spaces is closed under retaining
one bounded free-monomial coefficient. -/
theorem coefficient_projection_mem (S : Submodule K (Piece K t w 1))
    (C : (i : Fin (Fintype.card (BoundedExponent w 1))) → Submodule K (CoreBlock K t w 1 i))
    (hS : S.map orderedPiecesEquiv.toLinearMap=Submodule.pi Set.univ C)
    (x : Piece K t w 1) (hx : x ∈ S) (b : BoundedExponent w 1) :
    boundedInsert b (quotientPiecesEquiv x b) ∈ S := by
  classical
  have hX : orderedPiecesEquiv x ∈ Submodule.pi Set.univ C := by
    rw [←hS]
    exact ⟨x,hx,rfl⟩
  have hY : orderedPiecesEquiv (boundedInsert b (quotientPiecesEquiv x b)) ∈
      Submodule.pi Set.univ C := by
    intro j _
    rw [orderedPiecesEquiv_apply,quotientPiecesEquiv_boundedInsert]
    by_cases he : enumerate w 1 j=b
    · subst b
      simpa only [Pi.single_eq_same,orderedPiecesEquiv_apply] using hX j (Set.mem_univ j)
    · rw [Pi.single_eq_of_ne he]
      exact (C j).zero_mem
  rw [←hS] at hY
  obtain ⟨y,hy,heq⟩ := hY
  exact (orderedPiecesEquiv.injective heq) ▸ hy

/-- The bounded constant free monomial. -/
def zeroBounded (w : ℕ) : BoundedExponent w 1 := ⟨0,by simp⟩
/-- The bounded free monomial consisting of one variable. -/
def oneBounded (i : Fin w) : BoundedExponent w 1 :=
  ⟨(oneExponentEquiv i).val,by rw [(oneExponentEquiv i).property]⟩

theorem projection_core (x : Piece K t w 1) :
    boundedInsert (zeroBounded w) (quotientPiecesEquiv x (zeroBounded w))=
      insertAt (zeroExponent w) (degreeOneEquiv x).1 := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  rw [quotientPiecesEquiv_mk,boundedInsert_mk,degreeOneEquiv_mk_core,insertAt_mk]
  apply congrArg (relations K t w 1).mkQ
  funext r
  apply Subtype.ext
  simp only [targetCast_apply_val,ConvolutionFreeMultiplication.rowLift_apply_val,targetPiecesEquiv_apply_val]
  rfl

theorem projection_free (x : Piece K t w 1) (i : Fin w) :
    boundedInsert (oneBounded i) (quotientPiecesEquiv x (oneBounded i))=
      insertAt (oneExponentEquiv i) ((degreeOneEquiv x).2 i) := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  rw [quotientPiecesEquiv_mk,boundedInsert_mk,degreeOneEquiv_mk_free,insertAt_mk]
  apply congrArg (relations K t w 1).mkQ
  funext r
  apply Subtype.ext
  simp only [targetCast_apply_val,ConvolutionFreeMultiplication.rowLift_apply_val,targetPiecesEquiv_apply_val]
  rfl

/-- Core coordinate extraction in the actual degree-one decomposition. -/
def coreProjection : Piece K t w 1 →ₗ[K] Piece K t 0 1 :=
  (LinearMap.fst K (Piece K t 0 1) (Fin w → Piece K t 0 0)).comp degreeOneEquiv.toLinearMap

/-- Output coordinate extraction at one free variable. -/
def freeProjection (i : Fin w) : Piece K t w 1 →ₗ[K] Piece K t 0 0 :=
  (LinearMap.proj i).comp ((LinearMap.snd K (Piece K t 0 1) (Fin w → Piece K t 0 0)).comp
    degreeOneEquiv.toLinearMap)

def corePart (S : Submodule K (Piece K t w 1)) : Submodule K (Piece K t 0 1) :=
  S.map coreProjection

def freePart (S : Submodule K (Piece K t w 1)) (i : Fin w) : Submodule K (Piece K t 0 0) :=
  S.map (freeProjection i)

theorem reconstruct_degreeOne (x : Piece K t w 1) :
    insertAt (zeroExponent w) (degreeOneEquiv x).1+
      (∑i,insertAt (oneExponentEquiv i) ((degreeOneEquiv x).2 i))=x := by
  classical
  apply degreeOneEquiv.injective
  simp only [map_add,map_sum,degreeOne_insert_core,degreeOne_insert_free]
  apply Prod.ext
  · simp [Prod.fst_sum]
  · ext i
    simp [Prod.snd_sum,Finset.sum_apply,Pi.single_apply]

/-- Any full degree-one coefficient product is precisely its core/output split. -/
theorem coefficient_product_eq_split (S : Submodule K (Piece K t w 1))
    (C : (i : Fin (Fintype.card (BoundedExponent w 1))) → Submodule K (CoreBlock K t w 1 i))
    (hS : S.map orderedPiecesEquiv.toLinearMap=Submodule.pi Set.univ C) :
    S=splitSource (corePart S) (freePart S) := by
  apply le_antisymm
  · intro x hx
    rw [mem_splitSource]
    exact ⟨⟨x,hx,rfl⟩,fun i => ⟨x,hx,rfl⟩⟩
  · intro x hx
    obtain ⟨hxcore,hxfree⟩ := (mem_splitSource _ _ x).mp hx
    rw [←reconstruct_degreeOne x]
    apply S.add_mem
    · obtain ⟨y,hy,heq⟩ := hxcore
      have hp := coefficient_projection_mem S C hS y hy (zeroBounded w)
      rw [projection_core] at hp
      change (degreeOneEquiv y).1=(degreeOneEquiv x).1 at heq
      simpa only [heq] using hp
    · apply S.sum_mem
      intro i _
      obtain ⟨y,hy,heq⟩ := hxfree i
      have hp := coefficient_projection_mem S C hS y hy (oneBounded i)
      rw [projection_free] at hp
      change (degreeOneEquiv y).2 i=(degreeOneEquiv x).2 i at heq
      simpa only [heq] using hp

/-- The actual filtered initial subspace has exactly the split form required
by the convolution profile construction. -/
theorem initial_eq_split (S : Submodule K (Piece K t w 1)) :
    initial S=splitSource (corePart (initial S)) (freePart (initial S)) :=
  coefficient_product_eq_split (initial S) (initialCoefficients S) (map_initial S)

/-- Every actual subspace admits a split source of the same dimension whose
actual quadratic image has no larger dimension. -/
theorem exists_split_replacement (S : Submodule K (Piece K t w 1)) :
    ∃L : Submodule K (Piece K t 0 1), ∃D : Fin w → Submodule K (Piece K t 0 0),
      Module.finrank K (splitSource L D)=Module.finrank K S ∧
      Module.finrank K (ConvolutionProfileImage.quadraticImage (splitSource L D)) ≤
        Module.finrank K (ConvolutionProfileImage.quadraticImage S) := by
  refine ⟨corePart (initial S),freePart (initial S),?_,?_⟩
  · rw [←initial_eq_split]
    exact initial_finrank S
  · rw [←initial_eq_split]
    exact quadraticImage_initial_finrank_le S

end Quartic.ConvolutionInitialSplit
