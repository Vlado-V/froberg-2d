import Froberg.PrivateTypedRestoration
import Froberg.EvenFormalRelations
import Froberg.BiformSplitEndpoint
import Froberg.SupportedDeletionProjection

/-! The even and private-odd reductions combine into a literal full
coefficient boundary, leaving precisely the scalar background relations. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]

section Boundary
variable {V : Type*} [AddCommGroup V] [Module K V] {r b : ℕ}

def splitDiagonalMatrix (M : Fin r → Fin r → K) (C : Fin b → Fin b → K) :
    Fin (r+b) → Fin (r+b) → K := fun i j =>
  match finSumFinEquiv.symm i,finSumFinEquiv.symm j with
  | Sum.inl i,Sum.inl j => M i j
  | Sum.inr i,Sum.inr j => C i j
  | _,_ => 0

theorem coefficientBoundary_split_left (q : Fin (r+b) → V)
    (M : Fin r → Fin r → K) (C : Fin b → Fin b → K) (i : Fin r) :
    coefficientBoundary q (splitDiagonalMatrix M C) (finSumFinEquiv (Sum.inl i))=
      coefficientBoundary (fun j => q (finSumFinEquiv (Sum.inl j))) M i := by
  unfold coefficientBoundary
  rw [←finSumFinEquiv.sum_comp (fun j => splitDiagonalMatrix M C (finSumFinEquiv (Sum.inl i)) j • q j),
    ←finSumFinEquiv.sum_comp (fun j => splitDiagonalMatrix M C j (finSumFinEquiv (Sum.inl i)) • q j)]
  simp [Fintype.sum_sum_type,splitDiagonalMatrix]

theorem coefficientBoundary_split_right (q : Fin (r+b) → V)
    (M : Fin r → Fin r → K) (C : Fin b → Fin b → K) (i : Fin b) :
    coefficientBoundary q (splitDiagonalMatrix M C) (finSumFinEquiv (Sum.inr i))=
      coefficientBoundary (fun j => q (finSumFinEquiv (Sum.inr j))) C i := by
  unfold coefficientBoundary
  rw [←finSumFinEquiv.sum_comp (fun j => splitDiagonalMatrix M C (finSumFinEquiv (Sum.inr i)) j • q j),
    ←finSumFinEquiv.sum_comp (fun j => splitDiagonalMatrix M C j (finSumFinEquiv (Sum.inr i)) • q j)]
  simp [Fintype.sum_sum_type,splitDiagonalMatrix]
end Boundary

variable {h m d r b : ℕ}

def evenRestorationBiform (g : evenRestorationSpace (K := K) (blockWeight h m) d) :
    biformParitySpace K h m d 0 :=
  ⟨g.val,g.property.1,(parity_homogeneous_iff _ _ 0 (by decide)).mpr
    ((mem_weightedParitySpace_iff _ _ _).mp g.property.2)⟩

def oddRestorationBiform (g : oddRestorationSpace (K := K) (blockWeight h m) d) :
    biformParitySpace K h m d 1 :=
  ⟨g.val,g.property.1,(parity_homogeneous_iff _ _ 1 (by decide)).mpr
    ((mem_weightedParitySpace_iff _ _ _).mp g.property.2)⟩

def privateSplitEndpoint
    (g : Fin r → evenRestorationSpace (K := K) (blockWeight h m) d)
    (p : Fin b → oddRestorationSpace (K := K) (blockWeight h m) d) :
    Fin (r+b) → Forms K (h+m) d :=
  biformSplitEndpoint (fun i => evenRestorationBiform (g i)) (fun i => oddRestorationBiform (p i))

theorem privateSplitEndpoint_back
    (g : Fin r → evenRestorationSpace (K := K) (blockWeight h m) d)
    (p : Fin b → oddRestorationSpace (K := K) (blockWeight h m) d) (i : Fin r ⊕ Fin b) :
    rename finSumFinEquiv.symm (privateSplitEndpoint g p (finSumFinEquiv i)).val=
      Sum.elim (fun j => (g j).val) (fun j => (p j).val) i :=
  biformSplitEndpoint_back _ _ i

theorem private_split_supported_relations (htwo : (2 : K)≠0)
    (g : Fin r → evenRestorationSpace (K := K) (blockWeight h m) d)
    (p : Fin b → oddRestorationSpace (K := K) (blockWeight h m) d)
    (hi : LinearIndependent K (privateSplitEndpoint g p))
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range)
    (hodd : ∀ a : (endpointMultiplication (privateSplitEndpoint g p)).ker,
      (∀ i,(a.val i).val.IsWeightedHomogeneous (coreParity h m)
        (1-biformSplitEndpointParity (q := r) (f := b) i)) →
      a.val∈oppositeKoszulSpace (privateSplitEndpoint g p) (biformSplitEndpointParity (q := r) (f := b)))
    (degree : Fin r → ℕ) (Q : Submodule K (Forms K (h+m) d))
    (hQ : Q≤Submodule.span K (Set.range (privateSplitEndpoint g p)))
    (hlabel : ∀ i,degree i=0 → privateSplitEndpoint g p (finSumFinEquiv (Sum.inl i))∈Q)
    (hreduce : ∀ (c : Fin r → evenRestorationSpace (K := K) (blockWeight h m) d)
      (v : Fin b → oddRestorationSpace (K := K) (blockWeight h m) d),
      SplitRestoration.row (evenRestorationSpace (blockWeight h m) d).subtype
        (oddRestorationSpace (blockWeight h m) d).subtype (positiveWeightProjection (blockWeight h m) d)
        g p (c,v)=0 →
      ∃ (M : Fin r → Fin r → K) (C : Fin b → Fin b → K)
        (z : retainedScalarCoefficients (K := K) (blockWeight h m) d degree),
        c-coefficientBoundary g M=z.val ∧ v=coefficientBoundary p C) :
    (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalMixed (Submodule.span K (Set.range (privateSplitEndpoint g p)))=
      (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalProducts Q (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range := by
  classical
  apply projected_formal_relations_of_even_reduction htwo (coreParity h m)
    (biformSplitEndpointParity (q := r) (f := b)) (privateSplitEndpoint g p) hi
    (biformSplitEndpoint_parity _ _) D.mkQ (supported_deletion_odd_zero D hD)
    hodd Q _ hQ
  intro c hc
  let idx : Fin r ⊕ Fin b ≃ Fin (r+b) := finSumFinEquiv
  have hpar (i : Fin r ⊕ Fin b) :
      (rename finSumFinEquiv.symm (c.val (idx i)).val).IsWeightedHomogeneous
        (fun x => (blockWeight h m x : ZMod 2)) (0-biformSplitParity i) := by
    apply weighted_homogeneous_rename finSumFinEquiv.symm.toEmbedding
    have hh := hc (idx i)
    simpa only [biformSplitEndpointParity,Function.comp_apply,idx,Equiv.symm_apply_apply,
      coreParity_eq_blockParity,Equiv.coe_toEmbedding] using hh
  let cE : Fin r → evenRestorationSpace (K := K) (blockWeight h m) d := fun i =>
    ⟨rename finSumFinEquiv.symm (c.val (idx (Sum.inl i))).val,
      (c.val (idx (Sum.inl i))).property.rename_isHomogeneous,by
        apply (mem_weightedParitySpace_iff _ _ _).mpr
        apply (parity_homogeneous_iff _ _ 0 (by decide)).mp
        convert hpar (Sum.inl i) using 1 <;> norm_num [biformSplitParity] <;> decide⟩
  let cO : Fin b → oddRestorationSpace (K := K) (blockWeight h m) d := fun i =>
    ⟨rename finSumFinEquiv.symm (c.val (idx (Sum.inr i))).val,
      (c.val (idx (Sum.inr i))).property.rename_isHomogeneous,by
        apply (mem_weightedParitySpace_iff _ _ _).mpr
        apply (parity_homogeneous_iff _ _ 1 (by decide)).mp
        convert hpar (Sum.inr i) using 1 <;> norm_num [biformSplitParity] <;> decide⟩
  have hsum : rename finSumFinEquiv.symm (endpointMultiplication (privateSplitEndpoint g p) c.val).val=
      (∑ i,(g i).val*(cE i).val)+(∑ j,(p j).val*(cO j).val) := by
    rw [endpointMultiplication_val]
    simp only [map_sum,map_mul]
    rw [←idx.sum_comp (fun k => rename finSumFinEquiv.symm (privateSplitEndpoint g p k).val*
      rename finSumFinEquiv.symm (c.val k).val)]
    simp only [idx,privateSplitEndpoint_back,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,cE,cO]
  have hcD : endpointMultiplication (privateSplitEndpoint g p) c.val∈D := by
    have hh : endpointMultiplication (privateSplitEndpoint g p) c.val∈D.mkQ.ker := c.property
    rwa [Submodule.ker_mkQ] at hh
  obtain ⟨s,hs⟩ := hD hcD
  have hscalar : (rename finSumFinEquiv.symm
      (endpointMultiplication (privateSplitEndpoint g p) c.val).val).IsWeightedHomogeneous (blockWeight h m) 0 := by
    rw [←hs]
    apply weighted_homogeneous_rename finSumFinEquiv.symm.toEmbedding
    simpa only [←coreWeight_eq_blockWeight,Equiv.coe_toEmbedding,renameForm,LinearMap.coe_mk,AddHom.coe_mk] using scalar_rename_core_weight_zero (h := h) s
  have hrow : SplitRestoration.row (evenRestorationSpace (blockWeight h m) d).subtype
      (oddRestorationSpace (blockWeight h m) d).subtype (positiveWeightProjection (blockWeight h m) d)
      g p (cE,cO)=0 := by
    change positiveWeightProjection (blockWeight h m) d (∑ i,(g i).val*(cE i).val)+
      positiveWeightProjection (blockWeight h m) d (∑ j,(p j).val*(cO j).val)=0
    rw [←map_add,←hsum]
    exact positiveWeightProjection_zero _ _ _ hscalar
  obtain ⟨M,C,z,hz,hv⟩ := hreduce cE cO hrow
  let zE : Fin r → Forms K (h+m) d := fun i =>
    ⟨rename finSumFinEquiv (z.val i).val,(z.val i).property.1.rename_isHomogeneous⟩
  let z' : Fin (r+b) → Forms K (h+m) d := fun i =>
    Sum.elim zE (fun _ => 0) (idx.symm i)
  have hzE (i : Fin r) : z' (idx (Sum.inl i))=zE i := by
    simp only [z',Equiv.symm_apply_apply,Sum.elim_inl]
  have hzO (i : Fin b) : z' (idx (Sum.inr i))=0 := by
    simp only [z',Equiv.symm_apply_apply,Sum.elim_inr]
  have hcancel (v : MvPolynomial (Fin h ⊕ Fin m) K) :
      rename finSumFinEquiv.symm (rename finSumFinEquiv v)=v :=
    (renameEquiv K finSumFinEquiv).left_inv v
  refine ⟨splitDiagonalMatrix M C,z',?_,?_,?_⟩
  · funext k
    obtain ⟨k,rfl⟩ := idx.surjective k
    cases k with
    | inl i =>
      change c.val (finSumFinEquiv (Sum.inl i))-
        coefficientBoundary (privateSplitEndpoint g p) (splitDiagonalMatrix M C) (finSumFinEquiv (Sum.inl i))=_
      rw [coefficientBoundary_split_left]
      apply Subtype.ext
      apply (renameEquiv K finSumFinEquiv.symm).injective
      have hh := congrArg Subtype.val (congrFun hz i)
      simpa only [z',zE,idx,Equiv.symm_apply_apply,Sum.elim_inl,coefficientBoundary,
        Pi.sub_apply,Submodule.coe_sub,Submodule.coe_sum,Submodule.coe_smul,
        renameEquiv_apply,map_sub,map_sum,map_smul,privateSplitEndpoint_back,cE,
        hcancel] using hh
    | inr i =>
      change c.val (finSumFinEquiv (Sum.inr i))-
        coefficientBoundary (privateSplitEndpoint g p) (splitDiagonalMatrix M C) (finSumFinEquiv (Sum.inr i))=_
      rw [coefficientBoundary_split_right]
      apply Subtype.ext
      apply (renameEquiv K finSumFinEquiv.symm).injective
      have hh := congrArg Subtype.val (congrFun hv i)
      have hh' := sub_eq_zero.mpr hh
      simpa only [z',idx,Equiv.symm_apply_apply,Sum.elim_inr,coefficientBoundary,
        Submodule.coe_sub,Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_zero,
        renameEquiv_apply,map_sub,map_sum,map_smul,map_zero,privateSplitEndpoint_back,cO] using hh'
  · intro k
    obtain ⟨k,rfl⟩ := idx.surjective k
    cases k with
    | inl i =>
      by_cases hi0 : degree i=0
      · exact Or.inr (hlabel i hi0)
      · left
        rw [hzE]
        apply Subtype.ext
        have hz0 := congrArg Subtype.val (z.property.1 i (by omega))
        change rename finSumFinEquiv (z.val i).val=0
        rw [hz0,Submodule.coe_zero,map_zero]
    | inr i =>
      left
      simp [z',idx]
  · intro k
    obtain ⟨k,rfl⟩ := idx.surjective k
    cases k with
    | inl i =>
      rw [hzE]
      apply core_weight_zero_mem_scalar_range
      change (rename finSumFinEquiv (z.val i).val).IsWeightedHomogeneous (coreWeight h m) 0
      rw [coreWeight_eq_blockWeight]
      apply weighted_homogeneous_rename finSumFinEquiv.toEmbedding
      simpa only [Function.comp_def,Equiv.coe_toEmbedding,Equiv.symm_apply_apply] using z.property.2 i
    | inr i =>
      rw [hzO]
      exact Submodule.zero_mem _

end Froberg
