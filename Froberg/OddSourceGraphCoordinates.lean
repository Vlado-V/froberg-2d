module

public import Froberg.OddSourceBaseCoordinates
public import Froberg.ProjectedQuotientEquiv

@[expose] public section

/-! The remaining private generators give their literal graph relations
after the outer linear forms have been removed from the odd source. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d f u : ℕ}

abbrev OddBottomQuotient (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :=
  OddBottomTensor K h m d ⧸ Submodule.span K (Set.range F)

instance oddBottomQuotientGroup (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    AddCommGroup (OddBottomQuotient F) := Submodule.Quotient.addCommGroup _

instance oddBottomQuotientModule (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    Module K (OddBottomQuotient F) := Submodule.Quotient.module _

abbrev OddSourceBaseSpace (hd : 1≤d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :=
  OddBottomQuotient F × HigherOddCoordinates K h m d hd

instance oddSourceBaseSpaceGroup (hd : 1≤d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    AddCommGroup (OddSourceBaseSpace hd F) := Prod.instAddCommGroup

instance oddSourceBaseSpaceModule (hd : 1≤d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    Module K (OddSourceBaseSpace hd F) := Prod.instModule

def oddSourceBaseMap (hd : 1≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    biformParitySpace K h m d 1 →ₗ[K] OddBottomQuotient F × HigherOddCoordinates K h m d hd :=
  (oddSourceBaseEquiv hd F).toLinearMap.comp
    (Submodule.span K (Set.range (fun i => oddBiformEmbedding (t := 1) hd (by decide) (F i)))).mkQ

@[simp] theorem oddSourceBaseMap_apply (hd : 1≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) (p : biformParitySpace K h m d 1) :
    oddSourceBaseMap hd F p=
      ((Submodule.span K (Set.range F)).mkQ (oddSplitCoordinates hd p).1,
        (oddSplitCoordinates hd p).2) := rfl

theorem oddSourceBaseMap_surjective (hd : 1≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    Function.Surjective (oddSourceBaseMap hd F) :=
  (oddSourceBaseEquiv hd F).surjective.comp (Submodule.mkQ_surjective _)

theorem oddSourceBaseMap_kernel (hd : 1≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    (oddSourceBaseMap hd F).ker=Submodule.span K
      (Set.range (fun i => oddBiformEmbedding (t := 1) hd (by decide) (F i))) := by
  ext p
  change (oddSourceBaseEquiv hd F) ((Submodule.span K
    (Set.range (fun i => oddBiformEmbedding (t := 1) hd (by decide) (F i)))).mkQ p)=0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero _

def oddSourceRelationMap (hd : 1≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (G : Fin u → biformParitySpace K h m d 1) :
    (Fin u → K) →ₗ[K] OddBottomQuotient F × HigherOddCoordinates K h m d hd :=
  (oddSourceBaseMap hd F).comp (Fintype.linearCombination K G)

def oddBottomRelationMap (hd : 1≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (G : Fin u → biformParitySpace K h m d 1) :
    (Fin u → K) →ₗ[K] OddBottomQuotient F :=
  (LinearMap.fst K _ _).comp (oddSourceRelationMap hd F G)

def oddHigherRelationMap (hd : 1≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (G : Fin u → biformParitySpace K h m d 1) :
    (Fin u → K) →ₗ[K] HigherOddCoordinates K h m d hd :=
  (LinearMap.snd K _ _).comp (oddSourceRelationMap hd F G)

theorem oddSourceRelationMap_prod (hd : 1≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (G : Fin u → biformParitySpace K h m d 1) :
    (oddBottomRelationMap hd F G).prod (oddHigherRelationMap hd F G)=
      oddSourceRelationMap hd F G := by
  apply LinearMap.ext
  intro v
  rfl

def oddSourceGraphQuotientEquiv (hd : 1≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (G : Fin u → biformParitySpace K h m d 1) :
    (biformParitySpace K h m d 1 ⧸
      (Submodule.span K (Set.range (fun i => oddBiformEmbedding (t := 1) hd (by decide) (F i))) ⊔
        Submodule.span K (Set.range G))) ≃ₗ[K]
    (OddSourceBaseSpace hd F ⧸
      ((oddBottomRelationMap hd F G).prod (oddHigherRelationMap hd F G)).range) := by
  have hker := oddSourceBaseMap_kernel hd F
  have hrange : (Submodule.span K (Set.range G)).map (oddSourceBaseMap hd F)=
      ((oddBottomRelationMap hd F G).prod (oddHigherRelationMap hd F G)).range := by
    rw [oddSourceRelationMap_prod,oddSourceRelationMap,LinearMap.range_comp,
      Fintype.range_linearCombination]
  exact (Submodule.quotEquivOfEq _ _ (congrArg (fun S => S ⊔ Submodule.span K (Set.range G)) hker.symm)).trans
    ((projectedQuotientEquiv (oddSourceBaseMap hd F) (oddSourceBaseMap_surjective hd F)
      (Submodule.span K (Set.range G))).trans (Submodule.quotEquivOfEq _ _ hrange))

def oddSourceCoordinates (hd : 1≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (G : Fin u → biformParitySpace K h m d 1)
    (B : HigherOddCoordinates K h m d hd →ₗ[K] (Fin u → K))
    (hB : B.comp (oddHigherRelationMap hd F G)=LinearMap.id) :
    (biformParitySpace K h m d 1 ⧸
      (Submodule.span K (Set.range (fun i => oddBiformEmbedding (t := 1) hd (by decide) (F i))) ⊔
        Submodule.span K (Set.range G))) ≃ₗ[K]
      OddBottomQuotient F ×
        (HigherOddCoordinates K h m d hd ⧸ (oddHigherRelationMap hd F G).range) :=
  (oddSourceGraphQuotientEquiv hd F G).trans
    (graphQuotientCoordinates (oddBottomRelationMap hd F G) (oddHigherRelationMap hd F G) B hB)

@[simp] theorem oddSourceCoordinates_mk (hd : 1≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (G : Fin u → biformParitySpace K h m d 1)
    (B : HigherOddCoordinates K h m d hd →ₗ[K] (Fin u → K))
    (hB : B.comp (oddHigherRelationMap hd F G)=LinearMap.id)
    (p : biformParitySpace K h m d 1) :
    oddSourceCoordinates hd F G B hB
      ((Submodule.span K (Set.range (fun i => oddBiformEmbedding (t := 1) hd (by decide) (F i))) ⊔
        Submodule.span K (Set.range G)).mkQ p)=
      ((oddSourceBaseMap hd F p).1-oddBottomRelationMap hd F G (B (oddSourceBaseMap hd F p).2),
        (oddHigherRelationMap hd F G).range.mkQ (oddSourceBaseMap hd F p).2) := rfl

end Froberg
