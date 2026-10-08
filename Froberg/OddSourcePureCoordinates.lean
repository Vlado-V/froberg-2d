import Froberg.OddSourceGraphCoordinates
import Froberg.MixedPureComponents

/-! Independence of the fixed pure tuple supplies the actual graph
elimination needed for the odd source, for every private linear tuple P. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d f u : ℕ}

theorem oddHigherRelationMap_mixed_injective (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (hU : LinearIndependent K U)
    (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    Function.Injective (oddHigherRelationMap (by omega : 1≤d) F
      (fun i => mixedPureOddGenerator hd (U i) (P i))) := by
  let hd1 : 1≤d := by omega
  let G := fun i => mixedPureOddGenerator hd (U i) (P i)
  have hodd : d%2=1 := Nat.odd_iff.mp hd
  let r : {r : Fin ((d+1)/2) // r≠oddBottomIndex hd1} :=
    ⟨⟨(d-1)/2,by omega⟩,by
      intro he
      have hh := congrArg Fin.val he
      change (d-1)/2=0 at hh
      omega⟩
  have hr : 2*r.val.val+1=d := by dsimp [r];omega
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro c hc
  change (oddSplitCoordinates hd1 (Fintype.linearCombination K G c)).2=0 at hc
  have ht := congrFun hc r
  change oddBiformCoordinatesEquiv (Fintype.linearCombination K G c) r.val=0 at ht
  have hp := congrArg (sumBiformMap (K := K) (h := h) (n := m)
    (a := 2*r.val.val+1) (c := d-(2*r.val.val+1))) ht
  rw [oddBiformCoordinatesEquiv_component,map_zero,hr] at hp
  have hz : rename (Sum.inl : Fin h → Fin h ⊕ Fin m)
      (Fintype.linearCombination K U c).val=0 := by
    simpa only [Fintype.linearCombination_apply,Submodule.coe_sum,Submodule.coe_smul,
      map_sum,map_smul,G,mixedPureOddGenerator_top hd (by omega : 1<d)] using hp
  apply (linearIndependent_iff_injective_fintypeLinearCombination.mp hU)
  rw [map_zero]
  apply Subtype.ext
  apply rename_injective (Sum.inl : Fin h → Fin h ⊕ Fin m) Sum.inl_injective
  simpa only [Submodule.coe_zero,map_zero] using hz

theorem exists_odd_mixed_source_coordinates (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (hU : LinearIndependent K U)
    (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    ∃ B : HigherOddCoordinates K h m d (by omega : 1≤d) →ₗ[K] (Fin u → K),
      B.comp (oddHigherRelationMap (by omega : 1≤d) F
        (fun i => mixedPureOddGenerator hd (U i) (P i)))=LinearMap.id := by
  exact (oddHigherRelationMap (by omega : 1≤d) F
    (fun i => mixedPureOddGenerator hd (U i) (P i))).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (oddHigherRelationMap_mixed_injective hd hd3 F U hU P))

end Froberg
