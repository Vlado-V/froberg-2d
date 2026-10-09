module

public import Froberg.OddSourceBlockQuotients
public import Froberg.OddEndpointSourceCoordinates

@[expose] public section

/-! Actual endpoint source coordinates, with every higher odd block
retained and the bottom inclusion given by the literal linear biform. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}

abbrev OddMixedBlockCoordinates (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1)) :=
  (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex (Nat.le_trans (by decide : 1≤3) hd3)}) →
    (OddHigherBlock K h m d (Nat.le_trans (by decide : 1≤3) hd3) r ⧸
      coordinateRelation (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
        (fun i => mixedPureOddGenerator hd (U i) (P i))).range r)

instance oddMixedBlockCoordinatesGroup (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    AddCommGroup (OddMixedBlockCoordinates hd hd3 F U P) := Pi.addCommGroup

instance oddMixedBlockCoordinatesModule (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    Module K (OddMixedBlockCoordinates hd hd3 F U P) := Pi.module _ _ K

def oddMixedSourceBlockCoordinates (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (B : HigherOddCoordinates K h m d (Nat.le_trans (by decide : 1≤3) hd3) →ₗ[K] (Fin u → K))
    (hB : B.comp (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
      (fun i => mixedPureOddGenerator hd (U i) (P i)))=LinearMap.id) :
    (biformParitySpace K h m d 1 ⧸
      (Submodule.span K (Set.range (fun i => oddBiformEmbedding (t := 1) (Nat.le_trans (by decide : 1≤3) hd3) (by decide) (F i))) ⊔
        Submodule.span K (Set.range (fun i => mixedPureOddGenerator hd (U i) (P i))))) ≃ₗ[K]
      OddBottomQuotient F × OddMixedBlockCoordinates hd hd3 F U P :=
  (oddSourceCoordinates (Nat.le_trans (by decide : 1≤3) hd3) F
    (fun i => mixedPureOddGenerator hd (U i) (P i)) B hB).trans
    (LinearEquiv.prodCongr (LinearEquiv.refl K (OddBottomQuotient F))
      (oddHigherBlocksEquiv hd hd3 F U P))

theorem oddMixedSourceBlockCoordinates_bottom (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (B : HigherOddCoordinates K h m d (Nat.le_trans (by decide : 1≤3) hd3) →ₗ[K] (Fin u → K))
    (hB : B.comp (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
      (fun i => mixedPureOddGenerator hd (U i) (P i)))=LinearMap.id)
    (v : Forms K h 1 ⊗[K] Forms K m (d-1)) :
    oddMixedSourceBlockCoordinates hd hd3 F U P B hB
      (((Submodule.span K (Set.range (fun i => oddBiformEmbedding (t := 1) (Nat.le_trans (by decide : 1≤3) hd3) (by decide) (F i)))) ⊔
        Submodule.span K (Set.range (fun i => mixedPureOddGenerator hd (U i) (P i)))).mkQ
          (oddBiformEmbedding (t := 1) (Nat.le_trans (by decide : 1≤3) hd3) (by decide) v))=
      ((Submodule.span K (Set.range F)).mkQ v,0) := by
  rw [oddMixedSourceBlockCoordinates,LinearEquiv.trans_apply,oddSourceCoordinates_mk,
    oddSourceBaseMap_apply,oddSplitCoordinates_bottom]
  apply Prod.ext
  · change (Submodule.span K (Set.range F)).mkQ v-
      oddBottomRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
        (fun i => mixedPureOddGenerator hd (U i) (P i)) (B 0)=_
    rw [B.map_zero,(oddBottomRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
      (fun i => mixedPureOddGenerator hd (U i) (P i))).map_zero,sub_zero]
  · change oddHigherBlocksEquiv hd hd3 F U P
      ((oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
        (fun i => mixedPureOddGenerator hd (U i) (P i))).range.mkQ 0)=0
    rw [((oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
      (fun i => mixedPureOddGenerator hd (U i) (P i))).range.mkQ).map_zero]
    exact (oddHigherBlocksEquiv hd hd3 F U P).map_zero

def oddEndpointBlockCoordinates (hd : Odd d) (hd3 : 3≤d)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (B : HigherOddCoordinates K h m d (Nat.le_trans (by decide : 1≤3) hd3) →ₗ[K] (Fin u → K))
    (hB : B.comp (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
      (fun i => mixedPureOddGenerator hd (U i) (P i)))=LinearMap.id) :
    oddCoefficientSpace ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm)
      (backgroundEnumeratedForms Q
        (fun i => oddBiformEmbedding (t := 1) (Nat.le_trans (by decide : 1≤3) hd3) (by decide) (F i))
        (fun i => mixedPureOddGenerator hd (U i) (P i))) ≃ₗ[K]
      OddBottomQuotient F × OddMixedBlockCoordinates hd hd3 F U P :=
  (oddBackgroundSourceEquiv Q
    (fun i => oddBiformEmbedding (t := 1) (Nat.le_trans (by decide : 1≤3) hd3) (by decide) (F i))
    (fun i => mixedPureOddGenerator hd (U i) (P i))).symm.trans
      (oddMixedSourceBlockCoordinates hd hd3 F U P B hB)

theorem oddEndpointBlockCoordinates_bottom (hd : Odd d) (hd3 : 3≤d)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (B : HigherOddCoordinates K h m d (Nat.le_trans (by decide : 1≤3) hd3) →ₗ[K] (Fin u → K))
    (hB : B.comp (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
      (fun i => mixedPureOddGenerator hd (U i) (P i)))=LinearMap.id)
    (v : Forms K h 1 ⊗[K] Forms K m (d-1)) :
    oddEndpointBlockCoordinates hd hd3 Q F U P B hB
      (oddBackgroundSourceEquiv Q
        (fun i => oddBiformEmbedding (t := 1) (Nat.le_trans (by decide : 1≤3) hd3) (by decide) (F i))
        (fun i => mixedPureOddGenerator hd (U i) (P i))
        (((Submodule.span K (Set.range (fun i => oddBiformEmbedding (t := 1) (Nat.le_trans (by decide : 1≤3) hd3) (by decide) (F i)))) ⊔
          Submodule.span K (Set.range (fun i => mixedPureOddGenerator hd (U i) (P i)))).mkQ
            (oddBiformEmbedding (t := 1) (Nat.le_trans (by decide : 1≤3) hd3) (by decide) v)))=
      ((Submodule.span K (Set.range F)).mkQ v,0) := by
  rw [oddEndpointBlockCoordinates,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
  exact oddMixedSourceBlockCoordinates_bottom hd hd3 F U P B hB v

end Froberg
