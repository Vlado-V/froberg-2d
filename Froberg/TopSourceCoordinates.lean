module

public import Froberg.TopSourceProjection

@[expose] public section

/-! The top component of the actual source coordinates is precisely the
pure coefficient used by the ambient target-growth projection. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d f u b : ℕ}

theorem oddHigherBlocksEquiv_mk (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (v : HigherOddCoordinates K h m d (Nat.le_trans (by decide : 1≤3) hd3))
    (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex (Nat.le_trans (by decide : 1≤3) hd3)}) :
    oddHigherBlocksEquiv hd hd3 F U P
      ((oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
        (fun i => mixedPureOddGenerator hd (U i) (P i))).range.mkQ v) r=
      (coordinateRelation (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
        (fun i => mixedPureOddGenerator hd (U i) (P i))).range r).mkQ (v r) := rfl

theorem oddMixedSourceBlockCoordinates_higher (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (B : HigherOddCoordinates K h m d (Nat.le_trans (by decide : 1≤3) hd3) →ₗ[K] (Fin u → K))
    (hB : B.comp (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
      (fun i => mixedPureOddGenerator hd (U i) (P i)))=LinearMap.id)
    (v : biformParitySpace K h m d 1)
    (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex (Nat.le_trans (by decide : 1≤3) hd3)}) :
    (oddMixedSourceBlockCoordinates hd hd3 F U P B hB
      (((Submodule.span K (Set.range (fun i => oddBiformEmbedding (t := 1)
        (Nat.le_trans (by decide : 1≤3) hd3) (by decide) (F i)))) ⊔
        Submodule.span K (Set.range (fun i => mixedPureOddGenerator hd (U i) (P i)))).mkQ v)).2 r=
      (coordinateRelation (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
        (fun i => mixedPureOddGenerator hd (U i) (P i))).range r).mkQ
          (oddBiformCoordinatesEquiv v r.val) := rfl

theorem oddHigherPureEquiv_top_component (hdp : 1≤d)
    (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex hdp}) (hr : 2*r.val.val+1=d)
    (v : biformParitySpace K h m d 1) :
    (oddHigherPureEquiv (m := m) hdp r hr).symm (oddBiformCoordinatesEquiv v r.val)=
      topRowScalarCoefficient (biformTensorComponent le_rfl v) := by
  apply Subtype.ext
  apply rename_injective (Sum.inl : Fin h → Fin h ⊕ Fin m) Sum.inl_injective
  have h1 := sumBiformMap_oddHigherPureEquiv (m := m) hdp r hr
    ((oddHigherPureEquiv (m := m) hdp r hr).symm (oddBiformCoordinatesEquiv v r.val))
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [←h1,sumBiformMap_topRowScalarCoefficient,oddBiformCoordinatesEquiv_component,
    biformTensorComponent_spec,hr]

theorem oddMixedSourceBlockCoordinates_top_projection (hd : Odd d) (hd3 : 3≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (hR : Function.Surjective R)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (hker : R.ker=(Submodule.span K (Set.range U)).map
      (topGrowthDegree (Nat.le_trans (by decide : 1≤3) hd3) h).symm.toLinearMap)
    (B : HigherOddCoordinates K h m d (Nat.le_trans (by decide : 1≤3) hd3) →ₗ[K] (Fin u → K))
    (hB : B.comp (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
      (fun i => mixedPureOddGenerator hd (U i) (P i)))=LinearMap.id)
    (v : biformParitySpace K h m d 1)
    (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex (Nat.le_trans (by decide : 1≤3) hd3)})
    (hr : 2*r.val.val+1=d) :
    oddHigherTopProjectionEquiv hd hd3 R hR F U P hker r hr
      ((oddMixedSourceBlockCoordinates hd hd3 F U P B hB
        (((Submodule.span K (Set.range (fun i => oddBiformEmbedding (t := 1)
          (Nat.le_trans (by decide : 1≤3) hd3) (by decide) (F i)))) ⊔
          Submodule.span K (Set.range (fun i => mixedPureOddGenerator hd (U i) (P i)))).mkQ v)).2 r)=
      R ((topGrowthDegree (Nat.le_trans (by decide : 1≤3) hd3) h).symm
        (topRowScalarCoefficient (biformTensorComponent le_rfl v))) := by
  rw [oddMixedSourceBlockCoordinates_higher,oddHigherTopProjectionEquiv_mk,
    oddHigherPureEquiv_top_component]

end Froberg
