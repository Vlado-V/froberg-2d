import Froberg.RestoredEndpointPolynomial
import Froberg.PreparedCountExtension
import Froberg.PreparedPureRestoration
import Froberg.UpperTargetSpan

/-! A prepared high-target witness with separate pure generators embeds
in the actual restored even family by putting those pure forms in the
additional quadratic slots. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q r f e : ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

theorem restoredOuterEndpoint_renamed (hdp : 1≤d) (hd : d%2=0)
    {J : Finset ℕ} {counts : ℕ → ℕ}
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredOuterSpace m d q f J counts O) (i : Fin r ⊕ Fin f) :
    (restoredOuterEndpoint hdp hd hO hJ heven idx slot p (finSumFinEquiv i)).val=
      rename finSumFinEquiv (Sum.elim (fun j => (restoredFamilyLinear hd hO hJ heven idx slot p.1 j).val)
        (fun j => (p.2 j).val) i) := by
  have hh := congrArg (rename finSumFinEquiv) (restoredOuterEndpoint_back hdp hd hO hJ heven idx slot p i)
  have hc (z : Poly K (h+m)) : rename finSumFinEquiv (rename finSumFinEquiv.symm z)=z :=
    (renameEquiv K finSumFinEquiv).right_inv z
  rw [hc] at hh
  exact hh

def restoredUpperPoint (hd : 3≤d)
    (p : PreparedTarget.Space m d q f (finrank K (Forms K h d))
      (allEvenIndices d) (allEvenCount d h m e) O)
    (U : Fin (finrank K (Forms K h d)) → Forms K h d) :
    RestoredOuterSpace m d q f (allEvenIndices d)
      (allEvenCount d h m (e+finrank K (Forms K h d))) O :=
  ((extendQuadratic hd h m e _ p.1,U),p.2.1)

theorem restored_upper_point_contains (hd : 3≤d) (he : d%2=0)
    (hO : ∀ j∈allEvenIndices d,O j≤Forms K h j)
    (idx : Fin r ≃ Label q (allEvenIndices d)
      (allEvenCount d h m (e+finrank K (Forms K h d))))
    (p : PreparedTarget.Space m d q f (finrank K (Forms K h d))
      (allEvenIndices d) (allEvenCount d h m e) O) (hp : p.2.2=0)
    (U : Fin (finrank K (Forms K h d)) → Forms K h d)
    (i : PreparedTarget.Label q f (finrank K (Forms K h d))
      (allEvenIndices d) (allEvenCount d h m e)) :
    ∃ j : Fin (r+f),
      (restoredOuterEndpoint (by omega) he hO
        (fun j hj => (mem_allEvenIndices.mp hj).2.1)
        (fun j hj => (mem_allEvenIndices.mp hj).2.2) idx
        (fun k => idx.symm (quadraticTailSlot hd q h m e _ k))
        (restoredUpperPoint hd p U) j).val=
      PreparedTarget.renamedGenerator U (fun _ => 0) p i := by
  let slot := fun k => idx.symm (quadraticTailSlot hd q h m e (finrank K (Forms K h d)) k)
  rcases i with i | (i | i)
  · let j := idx.symm (countLabelMap (allEvenCount_le_append hd h m e _) i)
    refine ⟨finSumFinEquiv (Sum.inl j),?_⟩
    rw [restoredOuterEndpoint_renamed]
    simp only [Sum.elim_inl,PreparedTarget.renamedGenerator,PreparedTarget.generator_prepared]
    congr 1
    have haway : ∀ k,slot k≠j := by
      intro k hk
      apply quadraticTailSlot_ne_old hd h m e _ k i
      exact idx.symm.injective hk
    change generator (extendQuadratic hd h m e _ p.1) (idx j)+
      (PolynomialRestoration.pureShift (pureEvenEmbed he) slot U j).val=generator p.1 i
    rw [pureShift_eq_zero_away _ _ _ _ haway,Submodule.coe_zero,add_zero]
    dsimp only [j]
    rw [Equiv.apply_symm_apply]
    exact extendCounts_generator_old _ _ i
  · refine ⟨finSumFinEquiv (Sum.inr i),?_⟩
    rw [restoredOuterEndpoint_renamed]
    simp only [Sum.elim_inr,PreparedTarget.renamedGenerator,PreparedTarget.generator_outer]
    rfl
  · refine ⟨finSumFinEquiv (Sum.inl (slot i)),?_⟩
    rw [restoredOuterEndpoint_renamed]
    simp only [Sum.elim_inl,PreparedTarget.renamedGenerator,PreparedTarget.generator_private]
    congr 1
    have hslot : Function.Injective slot := idx.symm.injective.comp (quadraticTailSlot_injective hd q h m e _)
    change generator (extendQuadratic hd h m e _ p.1) (idx (slot i))+
      (PolynomialRestoration.pureShift (pureEvenEmbed he) slot U (slot i)).val=
      rename Sum.inr (p.2.2 i).val+(rename Sum.inl (U i).val+0)
    rw [pureShift_at_slot _ _ hslot]
    dsimp only [slot]
    rw [Equiv.apply_symm_apply,extendQuadratic_tail_zero,hp]
    simp only [Pi.zero_apply,Submodule.coe_zero,map_zero,zero_add,add_zero]
    rfl

theorem restored_upper_point_surjective (hd : 3≤d) (he : d%2=0)
    (hO : ∀ j∈allEvenIndices d,O j≤Forms K h j)
    (idx : Fin r ≃ Label q (allEvenIndices d)
      (allEvenCount d h m (e+finrank K (Forms K h d))))
    (p : PreparedTarget.Space m d q f (finrank K (Forms K h d))
      (allEvenIndices d) (allEvenCount d h m e) O) (hp : p.2.2=0)
    (U : Fin (finrank K (Forms K h d)) → Forms K h d)
    (hsurj : Function.Surjective (upperTargetMap
      (PreparedTarget.enumerateForms (PreparedTarget.forms (by omega) hO
        (fun j hj => (mem_allEvenIndices.mp hj).2.1) U (fun _ => 0)
        (fun _ => isHomogeneous_zero _ _ _) p)))) :
    Function.Surjective (upperTargetMap
      (restoredOuterEndpoint (by omega) he hO
        (fun j hj => (mem_allEvenIndices.mp hj).2.1)
        (fun j hj => (mem_allEvenIndices.mp hj).2.2) idx
        (fun k => idx.symm (quadraticTailSlot hd q h m e _ k)) (restoredUpperPoint hd p U))) := by
  apply upperTargetMap_surjective_of_span_le _ _ _ hsurj
  apply Submodule.span_mono
  rintro z ⟨i,rfl⟩
  have hh := restored_upper_point_contains hd he hO idx p hp U ((Fintype.equivFin _).symm i)
  exact hh

end Froberg.PreparedParameters
