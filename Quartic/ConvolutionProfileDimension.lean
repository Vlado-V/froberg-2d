module

public import Quartic.ConvolutionProfileImage

@[expose] public section

/-!
# Independent layer dimensions inside the actual quadratic image

Every chosen layer is placed in its own free-monomial coordinate of the checked
three-piece decomposition. Their product therefore injects into the actual
quadratic multiplication image of the split source.
-/

noncomputable section
namespace Quartic.ConvolutionProfileDimension
open FreeCoefficients FreeMonomialCounts ConvolutionFreePieces ConvolutionLayers
open FreeCoefficientProducts ConvolutionLayerInclusions ConvolutionProfileImage
variable {K : Type*} [Field K] {t w : ℕ}

/-- Product of the actual guaranteed subspaces in all three families of layers. -/
abbrev LayerDomain (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) :=
  (∀i,linearLayer L D i) ×
    (∀b:ExactExponent w 2,quadraticLayer L D b) ×
    (∀b:ExactExponent w 3,cubicLayer D b)

/-- Place every layer at its own free-monomial coordinate. -/
def assemble (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) : LayerDomain L D →ₗ[K] Piece K t w 3 where
  toFun x := (∑i,insertAt (oneExponentEquiv i) (x.1 i).val)+
    (∑b:ExactExponent w 2,insertAt b (x.2.1 b).val)+
    (∑b:ExactExponent w 3,insertAt b (x.2.2 b).val)
  map_add' x y := by
    simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply,Submodule.coe_add,map_add,Finset.sum_add_distrib]
    abel
  map_smul' a x := by
    simp only [Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,Submodule.coe_smul,
      map_smul,Finset.smul_sum,smul_add,RingHom.id_apply]

/-- The degree-three decomposition recovers every inserted coordinate. -/
theorem degreeThree_assemble (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) (x : LayerDomain L D) :
    degreeThreeEquiv (assemble L D x)=
      ((fun i => (x.1 i).val),(fun b => (x.2.1 b).val),(fun b => (x.2.2 b).val)) := by
  classical
  simp only [assemble,LinearMap.coe_mk,AddHom.coe_mk,map_add,map_sum,
    degreeThree_insert_linear,degreeThree_insert_quadratic,degreeThree_insert_cubic]
  apply Prod.ext
  · ext i
    simp [Prod.fst_sum,Finset.sum_apply,Pi.single_apply]
  · apply Prod.ext
    · ext b
      simp [Prod.fst_sum,Prod.snd_sum,Finset.sum_apply,Pi.single_apply]
    · ext b
      simp [Prod.snd_sum,Finset.sum_apply,Pi.single_apply]

theorem assemble_injective (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) : Function.Injective (assemble L D) := by
  intro x y h
  have heq := congrArg (fun z => degreeThreeEquiv z) h
  rw [degreeThree_assemble,degreeThree_assemble] at heq
  apply Prod.ext
  · funext i
    apply Subtype.ext
    exact congrArg (fun z => z.1 i) heq
  · apply Prod.ext
    · funext b
      apply Subtype.ext
      exact congrArg (fun z => z.2.1 b) heq
    · funext b
      apply Subtype.ext
      exact congrArg (fun z => z.2.2 b) heq

/-- Every assembled vector belongs to the genuine quadratic multiplication image. -/
theorem assemble_mem (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) (x : LayerDomain L D) :
    assemble L D x ∈ quadraticImage (splitSource L D) := by
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · apply Submodule.sum_mem
      intro i _
      exact linearLayer_mem L D i (x.1 i).property
    · apply Submodule.sum_mem
      intro b _
      exact quadraticLayer_mem L D b (x.2.1 b).property
  · apply Submodule.sum_mem
    intro b _
    exact cubicLayer_mem L D b (x.2.2 b).property

/-- An injective linear map from the entire product of layers into the actual image. -/
def assembleIntoImage (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) :
    LayerDomain L D →ₗ[K] quadraticImage (splitSource L D) :=
  (assemble L D).codRestrict _ (assemble_mem L D)

theorem assembleIntoImage_injective (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) : Function.Injective (assembleIntoImage L D) := by
  intro x y h
  apply assemble_injective L D
  exact congrArg Subtype.val h

/-- The three layer-rank sums are bounded by the dimension of the actual
quadratic image of the split source. -/
theorem layer_finrank_sum_le (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) :
    (∑i,Module.finrank K (linearLayer L D i))+
      (∑b:ExactExponent w 2,Module.finrank K (quadraticLayer L D b))+
      (∑b:ExactExponent w 3,Module.finrank K (cubicLayer D b)) ≤
    Module.finrank K (quadraticImage (splitSource L D)) := by
  have h := LinearMap.finrank_le_finrank_of_injective (assembleIntoImage_injective L D)
  simpa only [LayerDomain,Module.finrank_prod,Module.finrank_pi_fintype,Nat.add_assoc] using h

/-- The split source is linearly equivalent to its prescribed core and output
subspaces, with their actual vector-space structures. -/
def splitSourceEquiv (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) :
    splitSource L D ≃ₗ[K] L × (∀i,D i) where
  toFun x :=
    (⟨(degreeOneEquiv x.val).1,((mem_splitSource L D x.val).mp x.property).1⟩,
      fun i => ⟨(degreeOneEquiv x.val).2 i,((mem_splitSource L D x.val).mp x.property).2 i⟩)
  invFun x := ⟨degreeOneEquiv.symm (x.1.val,fun i => (x.2 i).val),by
    rw [mem_splitSource,LinearEquiv.apply_symm_apply]
    exact ⟨x.1.property,fun i => (x.2 i).property⟩⟩
  left_inv x := by
    apply Subtype.ext
    exact degreeOneEquiv.symm_apply_apply x.val
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (degreeOneEquiv.apply_symm_apply (x.1.val,fun i => (x.2 i).val))
    · funext i
      apply Subtype.ext
      exact congrArg (fun z => z.2 i) (degreeOneEquiv.apply_symm_apply (x.1.val,fun i => (x.2 i).val))
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      simp
    · funext i
      apply Subtype.ext
      simp
  map_smul' a x := by
    apply Prod.ext
    · apply Subtype.ext
      simp
    · funext i
      apply Subtype.ext
      simp

/-- Actual source dimension equals the core dimension plus all output-block dimensions. -/
theorem splitSource_finrank (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) :
    Module.finrank K (splitSource L D)=Module.finrank K L+∑i,Module.finrank K (D i) := by
  rw [(splitSourceEquiv L D).finrank_eq,Module.finrank_prod,Module.finrank_pi_fintype]

end Quartic.ConvolutionProfileDimension
