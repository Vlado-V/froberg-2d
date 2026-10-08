import Froberg.OddSourceHigherBlocks
import Froberg.BiformDegreeTransport

/-! Every non-top higher source block is unchanged. The top block is
exactly the pure degree-d space modulo the prescribed pure generators. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d f u : ℕ}

def oddTopHigherIndex (hd : Odd d) (hd3 : 3≤d) :
    {r : Fin ((d+1)/2) // r≠oddBottomIndex (Nat.le_trans (by decide : 1≤3) hd3)} := by
  have hodd := Nat.odd_iff.mp hd
  refine ⟨⟨(d-1)/2,by omega⟩,?_⟩
  intro he
  have hh := congrArg Fin.val he
  change (d-1)/2=0 at hh
  omega

@[simp] theorem oddTopHigherIndex_degree (hd : Odd d) (hd3 : 3≤d) :
    2*(oddTopHigherIndex hd hd3).val.val+1=d := by
  have hodd := Nat.odd_iff.mp hd
  change 2*((d-1)/2)+1=d
  omega

theorem oddHigherCoordinateRelation_eq_bot (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex (Nat.le_trans (by decide : 1≤3) hd3)})
    (hr : 2*r.val.val+1≠d) :
    coordinateRelation (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
      (fun i => mixedPureOddGenerator hd (U i) (P i))).range r=⊥ := by
  apply bot_unique
  intro x hx
  change x=0
  obtain ⟨y,⟨c,rfl⟩,he⟩ := hx
  change oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
    (fun i => mixedPureOddGenerator hd (U i) (P i)) c r=x at he
  exact he.symm.trans (oddHigherRelationMap_mixed_component_zero hd hd3 F U P r hr c)

def oddHigherNonTopQuotientEquiv (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex (Nat.le_trans (by decide : 1≤3) hd3)})
    (hr : 2*r.val.val+1≠d) :
    (OddHigherBlock K h m d (Nat.le_trans (by decide : 1≤3) hd3) r ⧸
      coordinateRelation (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
        (fun i => mixedPureOddGenerator hd (U i) (P i))).range r) ≃ₗ[K]
      OddHigherBlock K h m d (Nat.le_trans (by decide : 1≤3) hd3) r :=
  Submodule.quotEquivOfEqBot _ (oddHigherCoordinateRelation_eq_bot hd hd3 F U P r hr)

def oddHigherPureEquiv (hd1 : 1≤d)
    (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex hd1}) (hr : 2*r.val.val+1=d) :
    Forms K h d ≃ₗ[K] OddHigherBlock K h m d hd1 r :=
  (rightScalarBiformEquiv (m := m)).trans
    (biformDegreeTransport hr.symm (by omega : 0=d-(2*r.val.val+1)))

@[simp] theorem sumBiformMap_oddHigherPureEquiv (hd1 : 1≤d)
    (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex hd1}) (hr : 2*r.val.val+1=d)
    (v : Forms K h d) :
    sumBiformMap (oddHigherPureEquiv (m := m) hd1 r hr v)=rename Sum.inl v.val := by
  rw [oddHigherPureEquiv,LinearEquiv.trans_apply,sumBiformMap_degreeTransport,
    sumBiformMap_rightScalar]

theorem oddHigherRelationMap_mixed_top (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex (Nat.le_trans (by decide : 1≤3) hd3)})
    (hr : 2*r.val.val+1=d) (c : Fin u → K) :
    oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
      (fun i => mixedPureOddGenerator hd (U i) (P i)) c r=
        oddHigherPureEquiv (m := m) (Nat.le_trans (by decide : 1≤3) hd3) r hr (Fintype.linearCombination K U c) := by
  apply sumBiformMap_injective
  change sumBiformMap (oddBiformCoordinatesEquiv
    (Fintype.linearCombination K (fun i => mixedPureOddGenerator hd (U i) (P i)) c) r.val)=_
  rw [oddBiformCoordinatesEquiv_component,sumBiformMap_oddHigherPureEquiv,hr]
  simp only [Fintype.linearCombination_apply,Submodule.coe_sum,Submodule.coe_smul,
    map_sum,map_smul,mixedPureOddGenerator_top hd (by omega : 1<d)]

theorem oddHigherCoordinateRelation_top (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex (Nat.le_trans (by decide : 1≤3) hd3)})
    (hr : 2*r.val.val+1=d) :
    coordinateRelation (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
      (fun i => mixedPureOddGenerator hd (U i) (P i))).range r=
      (Submodule.span K (Set.range U)).map
        (oddHigherPureEquiv (m := m) (Nat.le_trans (by decide : 1≤3) hd3) r hr).toLinearMap := by
  rw [coordinateRelation,←LinearMap.range_comp]
  have he : (LinearMap.proj r).comp (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
      (fun i => mixedPureOddGenerator hd (U i) (P i)))=
      (oddHigherPureEquiv (m := m) (Nat.le_trans (by decide : 1≤3) hd3) r hr).toLinearMap.comp
        (Fintype.linearCombination K U) := by
    apply LinearMap.ext
    intro c
    exact oddHigherRelationMap_mixed_top hd hd3 F U P r hr c
  rw [he,LinearMap.range_comp,Fintype.range_linearCombination]

def oddHigherTopQuotientEquiv (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex (Nat.le_trans (by decide : 1≤3) hd3)})
    (hr : 2*r.val.val+1=d) :
    (OddHigherBlock K h m d (Nat.le_trans (by decide : 1≤3) hd3) r ⧸
      coordinateRelation (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
        (fun i => mixedPureOddGenerator hd (U i) (P i))).range r) ≃ₗ[K]
      (Forms K h d ⧸ Submodule.span K (Set.range U)) :=
  (Submodule.Quotient.equiv _ _ (oddHigherPureEquiv (m := m) (Nat.le_trans (by decide : 1≤3) hd3) r hr)
    (oddHigherCoordinateRelation_top hd hd3 F U P r hr).symm).symm

end Froberg
