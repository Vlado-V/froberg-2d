module

public import Froberg.OddSourcePureCoordinates
public import Froberg.CoordinateSubmodule

@[expose] public section

/-! The higher part of the odd source splits by every odd degree. The
private graph imposes relations only in the top source block. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d f u : ℕ}

abbrev OddHigherBlock (K : Type) [Field K] (h m d : ℕ) (hd : 1≤d)
    (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex hd}) :=
  Forms K h (2*r.val.val+1) ⊗[K] Forms K m (d-(2*r.val.val+1))

instance oddHigherBlockGroup (hd : 1≤d)
    (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex hd}) :
    AddCommGroup (OddHigherBlock K h m d hd r) := tensorFormGroup

instance oddHigherBlockModule (hd : 1≤d)
    (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex hd}) :
    Module K (OddHigherBlock K h m d hd r) := TensorProduct.leftModule

theorem oddHigherRelationMap_mixed_component_zero (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex (Nat.le_trans (by decide : 1≤3) hd3)})
    (hr : 2*r.val.val+1≠d) (c : Fin u → K) :
    oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
      (fun i => mixedPureOddGenerator hd (U i) (P i)) c r=0 := by
  have hr1 : 2*r.val.val+1≠1 := by
    intro he
    apply r.property
    apply Fin.ext
    change r.val.val=0
    omega
  apply sumBiformMap_injective
  change sumBiformMap (oddBiformCoordinatesEquiv
    (Fintype.linearCombination K (fun i => mixedPureOddGenerator hd (U i) (P i)) c) r.val)=sumBiformMap 0
  rw [oddBiformCoordinatesEquiv_component,map_zero]
  simp only [Fintype.linearCombination_apply,Submodule.coe_sum,Submodule.coe_smul,
    map_sum,map_smul,mixedPureOddGenerator_other hd hr1 hr,smul_zero,Finset.sum_const_zero]

theorem oddHigherRelationMap_mixed_range_single (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    ∀ x : HigherOddCoordinates K h m d (Nat.le_trans (by decide : 1≤3) hd3),x∈(oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
      (fun i => mixedPureOddGenerator hd (U i) (P i))).range →
      ∀ r : {r : Fin ((d+1)/2) // r≠oddBottomIndex (Nat.le_trans (by decide : 1≤3) hd3)},Pi.single r (x r)∈(oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
        (fun i => mixedPureOddGenerator hd (U i) (P i))).range := by
  classical
  rintro _ ⟨c,rfl⟩ r
  by_cases hr : 2*r.val.val+1=d
  · have he : Pi.single r (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
        (fun i => mixedPureOddGenerator hd (U i) (P i)) c r)=
        oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
          (fun i => mixedPureOddGenerator hd (U i) (P i)) c := by
      funext s
      by_cases hs : s=r
      · subst s
        exact Pi.single_eq_same _ _
      · rw [Pi.single_eq_of_ne hs]
        symm
        apply oddHigherRelationMap_mixed_component_zero hd hd3 F U P s _ c
        intro hsd
        apply hs
        apply Subtype.ext
        apply Fin.ext
        omega
    rw [he]
    exact ⟨c,rfl⟩
  · rw [oddHigherRelationMap_mixed_component_zero hd hd3 F U P r hr c]
    simpa only [Pi.single_zero] using (Submodule.zero_mem
      (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
        (fun i => mixedPureOddGenerator hd (U i) (P i))).range)

def oddHigherBlocksEquiv (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    (HigherOddCoordinates K h m d (Nat.le_trans (by decide : 1≤3) hd3) ⧸
      (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
        (fun i => mixedPureOddGenerator hd (U i) (P i))).range) ≃ₗ[K]
    ((r : {r : Fin ((d+1)/2) // r≠oddBottomIndex (Nat.le_trans (by decide : 1≤3) hd3)}) →
      (OddHigherBlock K h m d (Nat.le_trans (by decide : 1≤3) hd3) r) ⧸
        coordinateRelation (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
          (fun i => mixedPureOddGenerator hd (U i) (P i))).range r) :=
  coordinateQuotientEquiv _ (oddHigherRelationMap_mixed_range_single hd hd3 F U P)

end Froberg
