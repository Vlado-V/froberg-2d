module

public import Froberg.BiformSplitEndpoint

@[expose] public section

/-! Odd split exactness gives the actual opposite-parity Koszul conclusion
under any literal variable and generator enumeration. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u r : ℕ}

def indexedSplitParity (idx : Fin q ⊕ Fin f ≃ Fin r) : Fin r → ZMod 2 :=
  biformSplitParity ∘ idx.symm

theorem odd_split_endpoint_of_back
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (idx : Fin q ⊕ Fin f ≃ Fin r) (g : Fin r → Forms K (h+m) d)
    (hback : ∀ i,rename finSumFinEquiv.symm (g (idx i)).val=
      Sum.elim (fun j => (Q j).val) (fun j => (F j).val) i)
    (H : OddSplitExact Q F)
    (a : (endpointMultiplication g).ker)
    (ha : ∀ i,(a.val i).val.IsWeightedHomogeneous (coreParity h m)
      (1-indexedSplitParity idx i)) :
    a.val∈oppositeKoszulSpace g (indexedSplitParity idx) := by
  have hpar (i : Fin q ⊕ Fin f) :
      (rename finSumFinEquiv.symm (a.val (idx i)).val).IsWeightedHomogeneous
        (fun x => (blockWeight h m x : ZMod 2)) (1-biformSplitParity i) := by
    apply weighted_homogeneous_rename finSumFinEquiv.symm.toEmbedding
    have hh := ha (idx i)
    simpa only [indexedSplitParity,Function.comp_apply,Equiv.symm_apply_apply,
      coreParity_eq_blockParity,Equiv.coe_toEmbedding] using hh
  let c : Fin q → biformParitySpace K h m d 1 := fun i =>
    ⟨rename finSumFinEquiv.symm (a.val (idx (Sum.inl i))).val,
      (a.val (idx (Sum.inl i))).property.rename_isHomogeneous,by
        convert hpar (Sum.inl i) using 1 <;> norm_num [biformSplitParity]⟩
  let v : Fin f → biformParitySpace K h m d 0 := fun i =>
    ⟨rename finSumFinEquiv.symm (a.val (idx (Sum.inr i))).val,
      (a.val (idx (Sum.inr i))).property.rename_isHomogeneous,by
        convert hpar (Sum.inr i) using 1 <;> norm_num [biformSplitParity]⟩
  have hcycle : (∑ i,(Q i).val*(c i).val)+(∑ j,(F j).val*(v j).val)=0 := by
    have hz := congrArg (fun x : Forms K (h+m) (2*d) => rename finSumFinEquiv.symm x.val) a.property
    rw [endpointMultiplication_val] at hz
    simp only [map_sum,map_mul,Submodule.coe_zero,map_zero] at hz
    rw [←idx.sum_comp (fun k => rename finSumFinEquiv.symm (g k).val*
      rename finSumFinEquiv.symm (a.val k).val)] at hz
    simpa only [hback,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr] using hz
  obtain ⟨B,hB,hB'⟩ := H c v hcycle
  apply split_constants_mem_cross idx.symm (g) a.val B
  · intro i
    apply Subtype.ext
    apply (renameEquiv K finSumFinEquiv.symm).injective
    change (c i).val=rename finSumFinEquiv.symm
      (∑ j,B i j • g (idx (Sum.inr j))).val
    simpa only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,
      hback,Sum.elim_inr] using hB i
  · intro j
    apply Subtype.ext
    apply (renameEquiv K finSumFinEquiv.symm).injective
    change (v j).val=rename finSumFinEquiv.symm
      (-∑ i,B i j • g (idx (Sum.inl i))).val
    simpa only [Submodule.coe_neg,Submodule.coe_sum,Submodule.coe_smul,map_neg,map_sum,map_smul,
      hback,Sum.elim_inl] using hB' j


def backgroundSplitIndex : Fin q ⊕ Fin (f+u) ≃ Fin (Fintype.card (BackgroundLabel q f u)) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm).trans (Fintype.equivFin _)

theorem backgroundEnumeratedForms_back
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1) (i : BackgroundLabel q f u) :
    rename finSumFinEquiv.symm
      (backgroundEnumeratedForms Q F G ((Fintype.equivFin _) i)).val=
      (backgroundParityFamily Q F G i).val := by
  change rename finSumFinEquiv.symm (rename finSumFinEquiv
    (backgroundParityFamily Q F G ((Fintype.equivFin _).symm ((Fintype.equivFin _) i))).val)=_
  rw [Equiv.symm_apply_apply]
  exact (renameEquiv K finSumFinEquiv).left_inv _

theorem backgroundSplitIndex_back
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1) (i : Fin q ⊕ Fin (f+u)) :
    rename finSumFinEquiv.symm
      (backgroundEnumeratedForms Q F G (backgroundSplitIndex i)).val=
      Sum.elim (fun j => (Q j).val) (fun j => (Fin.append F G j).val) i := by
  change rename finSumFinEquiv.symm
    (backgroundEnumeratedForms Q F G ((Fintype.equivFin _)
      ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm) i))).val=_
  rw [backgroundEnumeratedForms_back]
  cases i with
  | inl j => rfl
  | inr j =>
      refine Fin.addCases ?_ ?_ j
      · intro k
        change (backgroundParityFamily Q F G (Sum.inr (finSumFinEquiv.symm (k.castAdd u)))).val=
          (Fin.append F G (k.castAdd u)).val
        rw [finSumFinEquiv_symm_apply_castAdd,Fin.append_left]
        rfl
      · intro k
        change (backgroundParityFamily Q F G (Sum.inr (finSumFinEquiv.symm (k.natAdd f)))).val=
          (Fin.append F G (k.natAdd f)).val
        rw [finSumFinEquiv_symm_apply_natAdd,Fin.append_right]
        rfl

theorem odd_split_background_endpoint
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (H : OddSplitExact Q (Fin.append F G))
    (a : (endpointMultiplication (backgroundEnumeratedForms Q F G)).ker)
    (ha : ∀ i,(a.val i).val.IsWeightedHomogeneous (coreParity h m)
      (1-indexedSplitParity (backgroundSplitIndex (q := q) (f := f) (u := u)) i)) :
    a.val∈oppositeKoszulSpace (backgroundEnumeratedForms Q F G)
      (indexedSplitParity (backgroundSplitIndex (q := q) (f := f) (u := u))) :=
  odd_split_endpoint_of_back Q (Fin.append F G) backgroundSplitIndex
    (backgroundEnumeratedForms Q F G) (backgroundSplitIndex_back Q F G) H a ha


theorem background_split_parity_eq :
    indexedSplitParity (backgroundSplitIndex (q := q) (f := f) (u := u))=
      backgroundParity ∘ (Fintype.equivFin (BackgroundLabel q f u)).symm := by
  funext k
  obtain ⟨i,rfl⟩ := (Fintype.equivFin (BackgroundLabel q f u)).surjective k
  rcases i with i | (i | i) <;>
    simp [indexedSplitParity,backgroundSplitIndex,biformSplitParity,backgroundParity]

theorem backgroundEnumeratedForms_split_parity
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (i : Fin (Fintype.card (BackgroundLabel q f u))) :
    (backgroundEnumeratedForms Q F G i).val.IsWeightedHomogeneous (coreParity h m)
      (indexedSplitParity (backgroundSplitIndex (q := q) (f := f) (u := u)) i) := by
  rw [background_split_parity_eq]
  simpa only [coreParity_eq_blockParity,backgroundEnumeratedForms,Function.comp_apply] using
    parityEnumeratedForms_homogeneous finSumFinEquiv (Fintype.equivFin _)
      (fun x => (blockWeight h m x : ZMod 2)) backgroundParity (backgroundParityFamily Q F G) i

end Froberg
