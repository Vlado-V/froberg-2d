module

public import Froberg.OddSplitComplex
public import Froberg.ParityPolynomialEndpoint
public import Froberg.OppositeCoefficientBoundary
public import Froberg.OddBackgroundBottomDetection

@[expose] public section

/-! A split biform odd-row calculation is the literal opposite-parity
Koszul statement for the ordinary enumerated polynomial endpoint. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}

def biformSplitParity : Fin q ⊕ Fin f → ZMod 2 := Sum.elim (fun _ => 0) (fun _ => 1)

def biformSplitFamily (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) :
    (i : Fin q ⊕ Fin f) → homogeneousParitySpace K (Fin h ⊕ Fin m) d
      (fun x => (blockWeight h m x : ZMod 2)) (biformSplitParity i)
  | Sum.inl i => Q i
  | Sum.inr i => F i

def biformSplitEndpoint (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) : Fin (q+f) → Forms K (h+m) d :=
  parityEnumeratedForms finSumFinEquiv finSumFinEquiv
    (fun x => (blockWeight h m x : ZMod 2)) biformSplitParity (biformSplitFamily Q F)

def biformSplitEndpointParity : Fin (q+f) → ZMod 2 := biformSplitParity ∘ finSumFinEquiv.symm

theorem biformSplitEndpoint_parity (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (i : Fin (q+f)) :
    (biformSplitEndpoint Q F i).val.IsWeightedHomogeneous (coreParity h m)
      (biformSplitEndpointParity (q := q) (f := f) i) := by
  simpa only [coreParity_eq_blockParity, biformSplitEndpoint, biformSplitEndpointParity,
    Function.comp_apply] using parityEnumeratedForms_homogeneous
    finSumFinEquiv finSumFinEquiv (fun x => (blockWeight h m x : ZMod 2))
    biformSplitParity (biformSplitFamily Q F) i

theorem biformSplitEndpoint_back (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (i : Fin q ⊕ Fin f) :
    rename finSumFinEquiv.symm (biformSplitEndpoint Q F (finSumFinEquiv i)).val=
      Sum.elim (fun j => (Q j).val) (fun j => (F j).val) i := by
  change rename finSumFinEquiv.symm (rename finSumFinEquiv
    (biformSplitFamily Q F (finSumFinEquiv.symm (finSumFinEquiv i))).val)=_
  rw [Equiv.symm_apply_apply]
  have hcancel (z : MvPolynomial (Fin h ⊕ Fin m) K) :
      rename finSumFinEquiv.symm (rename finSumFinEquiv z)=z := (renameEquiv K finSumFinEquiv).left_inv z
  rw [hcancel]
  cases i <;> rfl

theorem odd_split_endpoint (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (H : OddSplitExact Q F)
    (a : (endpointMultiplication (biformSplitEndpoint Q F)).ker)
    (ha : ∀ i,(a.val i).val.IsWeightedHomogeneous (coreParity h m)
      (1-biformSplitEndpointParity (q := q) (f := f) i)) :
    a.val∈oppositeKoszulSpace (biformSplitEndpoint Q F) (biformSplitEndpointParity (q := q) (f := f)) := by
  let idx : Fin q ⊕ Fin f ≃ Fin (q+f) := finSumFinEquiv
  have hpar (i : Fin q ⊕ Fin f) :
      (rename finSumFinEquiv.symm (a.val (idx i)).val).IsWeightedHomogeneous
        (fun x => (blockWeight h m x : ZMod 2)) (1-biformSplitParity i) := by
    apply weighted_homogeneous_rename finSumFinEquiv.symm.toEmbedding
    have hh := ha (idx i)
    simpa only [biformSplitEndpointParity,Function.comp_apply,idx,Equiv.symm_apply_apply,
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
    rw [←idx.sum_comp (fun k => rename finSumFinEquiv.symm (biformSplitEndpoint Q F k).val*
      rename finSumFinEquiv.symm (a.val k).val)] at hz
    simpa only [idx,biformSplitEndpoint_back,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr] using hz
  obtain ⟨B,hB,hB'⟩ := H c v hcycle
  apply split_constants_mem_cross idx.symm (biformSplitEndpoint Q F) a.val B
  · intro i
    apply Subtype.ext
    apply (renameEquiv K finSumFinEquiv.symm).injective
    change (c i).val=rename finSumFinEquiv.symm
      (∑ j,B i j • biformSplitEndpoint Q F (idx (Sum.inr j))).val
    simpa only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,idx,
      biformSplitEndpoint_back,Sum.elim_inr] using hB i
  · intro j
    apply Subtype.ext
    apply (renameEquiv K finSumFinEquiv.symm).injective
    change (v j).val=rename finSumFinEquiv.symm
      (-∑ i,B i j • biformSplitEndpoint Q F (idx (Sum.inl i))).val
    simpa only [Submodule.coe_neg,Submodule.coe_sum,Submodule.coe_smul,map_neg,map_sum,map_smul,idx,
      biformSplitEndpoint_back,Sum.elim_inl] using hB' j

end Froberg
