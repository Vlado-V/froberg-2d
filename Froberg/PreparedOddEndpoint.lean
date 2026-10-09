module

public import Froberg.PreparedOddCyclesOpen
public import Froberg.OppositeCoefficientBoundary
public import Froberg.OddBackgroundBottomDetection

@[expose] public section

/-! The literal odd-cycle constants of the prepared family give exactly
the opposite-parity Koszul space in the ordinary enumerated endpoint ring. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def splitParity : Label q f u J counts → ZMod 2 := Sum.elim (fun _ => 0) (fun _ => 1)

def zeroScalarEndpointFamily (hd : 0<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (p : PreparedParameters.Space m d q J counts O × OuterSpace K (Fin h) m d f) :
    Fin (Fintype.card (Label q f u J counts)) → Forms K (h+m) d :=
  enumerateForms (forms hd hO hJ U (fun i => (P i).val)
    (FullPreparedParameters.private_homogeneous hd P) (zeroPrivateScalar p))

def endpointSplitParity : Fin (Fintype.card (Label q f u J counts)) → ZMod 2 :=
  splitParity ∘ (Fintype.equivFin _).symm

theorem zeroScalarEndpointFamily_back (hd : 0<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (p : PreparedParameters.Space m d q J counts O × OuterSpace K (Fin h) m d f)
    (i : Label q f u J counts) :
    rename finSumFinEquiv.symm
      (zeroScalarEndpointFamily hd hO hJ U P p (Fintype.equivFin _ i)).val=
      Sum.elim (PreparedParameters.generator p.1) (oddGenerator U P p.2) i := by
  change rename finSumFinEquiv.symm (rename finSumFinEquiv
    ((forms hd hO hJ U (fun i => (P i).val)
      (FullPreparedParameters.private_homogeneous hd P) (zeroPrivateScalar p))
      ((Fintype.equivFin _).symm (Fintype.equivFin _ i))).val)=_
  rw [Equiv.symm_apply_apply]
  have hcancel (z : MvPolynomial (Fin h ⊕ Fin m) K) :
      rename finSumFinEquiv.symm (rename finSumFinEquiv z)=z :=
    (renameEquiv K finSumFinEquiv).left_inv z
  rw [hcancel]
  rcases i with i | (i | i)
  · simp only [forms_val,generator_prepared,zeroPrivateScalar_apply,Sum.elim_inl]
  · simp [forms_val,generator_outer,zeroPrivateScalar,oddGenerator,combinedLinear,combinedPure]
  · simp [forms_val,zeroPrivateScalar_generator_private,oddGenerator,combinedLinear,combinedPure,add_comm]

theorem odd_cycles_endpoint (hd : 0<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (p : PreparedParameters.Space m d q J counts O × OuterSpace K (Fin h) m d f)
    (H : OddCyclesExact U P p)
    (a : (endpointMultiplication (zeroScalarEndpointFamily hd hO hJ U P p)).ker)
    (ha : ∀ i,(a.val i).val.IsWeightedHomogeneous (coreParity h m)
      (1-endpointSplitParity (q := q) (f := f) (u := u) (J := J) (counts := counts) i)) :
    a.val∈oppositeKoszulSpace (zeroScalarEndpointFamily hd hO hJ U P p)
      (endpointSplitParity (q := q) (f := f) (u := u) (J := J) (counts := counts)) := by
  classical
  let idx := Fintype.equivFin (Label q f u J counts)
  let Q := zeroScalarEndpointFamily hd hO hJ U P p
  let c := fun i : PreparedParameters.Label q J counts =>
    rename finSumFinEquiv.symm (a.val (idx (Sum.inl i))).val
  let v := fun j : Fin f ⊕ Fin u =>
    rename finSumFinEquiv.symm (a.val (idx (Sum.inr j))).val
  have hpar (i : Label q f u J counts) :
      (rename finSumFinEquiv.symm (a.val (idx i)).val).IsWeightedHomogeneous
        (fun x => (blockWeight h m x : ZMod 2)) (1-splitParity i) := by
    apply weighted_homogeneous_rename finSumFinEquiv.symm.toEmbedding
    have hh := ha (idx i)
    simpa only [endpointSplitParity,Function.comp_apply,idx,Equiv.symm_apply_apply,
      coreParity_eq_blockParity,Equiv.coe_toEmbedding] using hh
  have hc : ∀ i,(c i).IsHomogeneous d := fun i => (a.val (idx (Sum.inl i))).property.rename_isHomogeneous
  have hv : ∀ j,(v j).IsHomogeneous d := fun j => (a.val (idx (Sum.inr j))).property.rename_isHomogeneous
  have hcp : ∀ i α,(c i).coeff α≠0 → Finsupp.weight (blockWeight h m) α%2=1 := by
    intro i
    apply (parity_homogeneous_iff (blockWeight h m) (c i) 1 (by decide)).mp
    convert hpar (Sum.inl i) using 1 <;> norm_num [splitParity]
  have hvp : ∀ j α,(v j).coeff α≠0 → Finsupp.weight (blockWeight h m) α%2=0 := by
    intro j
    apply (parity_homogeneous_iff (blockWeight h m) (v j) 0 (by decide)).mp
    convert hpar (Sum.inr j) using 1 <;> norm_num [splitParity]
  have hcycle : (∑ i,PreparedParameters.generator p.1 i*c i)+
      (∑ j,oddGenerator U P p.2 j*v j)=0 := by
    have hz := congrArg (fun x : Forms K (h+m) (2*d) => rename finSumFinEquiv.symm x.val) a.property
    rw [endpointMultiplication_val] at hz
    simp only [map_sum,map_mul,Submodule.coe_zero,map_zero] at hz
    rw [←idx.sum_comp (fun k => rename finSumFinEquiv.symm (Q k).val*
      rename finSumFinEquiv.symm (a.val k).val)] at hz
    simpa only [Q,idx,zeroScalarEndpointFamily_back,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr] using hz
  obtain ⟨B,hB,hB'⟩ := H c v hc hv hcp hvp hcycle
  apply split_constants_mem_cross idx.symm Q a.val B
  · intro i
    apply Subtype.ext
    apply (renameEquiv K finSumFinEquiv.symm).injective
    change c i=rename finSumFinEquiv.symm (∑ j,B i j • Q (idx (Sum.inr j))).val
    simpa only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,Q,idx,
      zeroScalarEndpointFamily_back,Sum.elim_inr] using hB i
  · intro j
    apply Subtype.ext
    apply (renameEquiv K finSumFinEquiv.symm).injective
    change v j=rename finSumFinEquiv.symm (-∑ i,B i j • Q (idx (Sum.inl i))).val
    simpa only [Submodule.coe_neg,Submodule.coe_sum,Submodule.coe_smul,map_neg,map_sum,map_smul,Q,idx,
      zeroScalarEndpointFamily_back,Sum.elim_inl] using hB' j

end Froberg.PreparedTarget
