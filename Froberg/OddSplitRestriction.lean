module

public import Froberg.OddSplitComplex
public import Froberg.PairKernelReindex

@[expose] public section

/-! Removing an initial block of odd generators preserves odd exactness
when the even generators are independent. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}

theorem odd_split_exact_restrict_right
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (hQ : LinearIndependent K Q) (H : OddSplitExact Q (Fin.append F G)) :
    OddSplitExact Q G := by
  classical
  intro c v hr
  have hrel : (∑ i,(Q i).val*(c i).val)+
      (∑ j,(Fin.append F G j).val*(Fin.append (fun _ : Fin f => (0 : biformParitySpace K h m d 0)) v j).val)=0 := by
    rw [Fin.sum_univ_add]
    simpa only [Fin.append_left,Fin.append_right,Submodule.coe_zero,mul_zero,Finset.sum_const_zero,zero_add] using hr
  obtain ⟨B,hB,hB'⟩ := H c (Fin.append (fun _ : Fin f => 0) v) hrel
  have hzero (i : Fin q) (j : Fin f) : B i (Fin.castAdd u j)=0 := by
    have hh := hB' (Fin.castAdd u j)
    simp only [Fin.append_left,Submodule.coe_zero] at hh
    have hs : (∑ k,B k (Fin.castAdd u j) • Q k)=0 := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_zero] using neg_eq_zero.mp hh.symm
    exact Fintype.linearIndependent_iff.mp hQ _ hs i
  refine ⟨fun i j => B i (Fin.natAdd f j),?_,?_⟩
  · intro i
    have hh := hB i
    rw [Fin.sum_univ_add] at hh
    simpa only [Fin.append_left,Fin.append_right,hzero,zero_smul,Finset.sum_const_zero,zero_add] using hh
  · intro j
    simpa only [Fin.append_right] using hB' (Fin.natAdd f j)


theorem odd_split_exact_reindex {q' u' : ℕ}
    (Q : Fin q → biformParitySpace K h m d 0)
    (G : Fin u → biformParitySpace K h m d 1)
    (e : Fin q' ≃ Fin q) (f : Fin u' ≃ Fin u) (H : OddSplitExact Q G) :
    OddSplitExact (fun i => Q (e i)) (fun j => G (f j)) := by
  intro c v hr
  apply constant_pair_kernel_reindex e f
    (fun i => (Q (e i)).val) (fun j => (G (f j)).val)
    (biformParitySpace K h m d 1) (biformParitySpace K h m d 0) ?_
    (fun i => (c i).val) (fun j => (v j).val)
    (fun i => (c i).property) (fun j => (v j).property) hr
  intro x y hx hy hxy
  obtain ⟨B,hB,hB'⟩ := H (fun i => ⟨x i,hx i⟩) (fun j => ⟨y j,hy j⟩)
    (by simpa only [Equiv.apply_symm_apply] using hxy)
  exact ⟨B,by simpa only [Equiv.apply_symm_apply] using hB,
    by simpa only [Equiv.apply_symm_apply] using hB'⟩

end Froberg
