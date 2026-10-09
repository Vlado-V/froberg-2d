module

public import Froberg.CycleReductionFormal
public import Froberg.ParityComplex

@[expose] public section

/-! Constant matrices supported across the two generator parities are
literal elements of the opposite-parity Koszul span. -/
noncomputable section
namespace Froberg
open Module Finset
variable {K : Type} {V : Type*} [Field K] [AddCommGroup V] [Module K V] {r : ℕ}

def orderedModuleKoszul (q : Fin r → V) (i j : Fin r) : Fin r → V :=
  fun k => (if k=i then q j else 0)-(if k=j then q i else 0)

theorem orderedModuleKoszul_mem_cross {P : Type*} (q : Fin r → V) (e : Fin r → P)
    (i j : Fin r) (hij : e i≠e j) :
    orderedModuleKoszul q i j∈Submodule.span K
      (koszulVector q '' {p : GeneratorPair r | e p.val.1≠e p.val.2}) := by
  classical
  rcases lt_trichotomy i j with hl|he|hl
  · exact Submodule.subset_span ⟨⟨(i,j),hl⟩,hij,rfl⟩
  · exact False.elim (hij (congrArg e he))
  · have hn : orderedModuleKoszul q i j = -koszulVector q ⟨(j,i),hl⟩ := by
      funext k
      simp only [orderedModuleKoszul,koszulVector,Pi.neg_apply,neg_sub]
    rw [hn]
    exact Submodule.neg_mem _ (Submodule.subset_span ⟨⟨(j,i),hl⟩,Ne.symm hij,rfl⟩)

theorem coefficientBoundary_eq_ordered_sum (q : Fin r → V) (C : Fin r → Fin r → K) :
    coefficientBoundary q C=∑ i,∑ j,C i j • orderedModuleKoszul q i j := by
  classical
  funext k
  simp only [coefficientBoundary,Finset.sum_apply,Pi.smul_apply,orderedModuleKoszul,
    smul_sub,smul_ite,smul_zero,sum_sub_distrib]
  congr 1
  · rw [sum_comm]
    simp
  · simp

theorem coefficientBoundary_mem_cross {P : Type*} (q : Fin r → V) (e : Fin r → P)
    (C : Fin r → Fin r → K) (hC : ∀ i j,e i=e j → C i j=0) :
    coefficientBoundary q C∈Submodule.span K
      (koszulVector q '' {p : GeneratorPair r | e p.val.1≠e p.val.2}) := by
  classical
  rw [coefficientBoundary_eq_ordered_sum]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  by_cases he : e i=e j
  · simp only [hC i j he,zero_smul]
    exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (orderedModuleKoszul_mem_cross q e i j he)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem split_constants_mem_cross (split : Fin r ≃ I ⊕ J) (q c : Fin r → V)
    (B : I → J → K)
    (hc : ∀ i,c (split.symm (Sum.inl i))=∑ j,B i j • q (split.symm (Sum.inr j)))
    (hc' : ∀ j,c (split.symm (Sum.inr j)) = -∑ i,B i j • q (split.symm (Sum.inl i))) :
    c∈Submodule.span K (koszulVector q '' {p : GeneratorPair r |
      (Sum.elim (fun _ : I => (0 : ZMod 2)) (fun _ : J => 1) (split p.val.1))≠
      (Sum.elim (fun _ : I => (0 : ZMod 2)) (fun _ : J => 1) (split p.val.2))}) := by
  classical
  let C : Fin r → Fin r → K := fun k l =>
    match split k,split l with
    | Sum.inl i,Sum.inr j => B i j
    | _,_ => 0
  have heq : c=coefficientBoundary q C := by
    funext k
    obtain ⟨z,rfl⟩ := split.symm.surjective k
    rw [coefficientBoundary]
    rw [←split.symm.sum_comp (fun l => C (split.symm z) l • q l),
      ←split.symm.sum_comp (fun l => C l (split.symm z) • q l)]
    cases z with
    | inl i => simpa [C] using hc i
    | inr j => simpa [C] using hc' j
  rw [heq]
  apply coefficientBoundary_mem_cross q
    (fun k => Sum.elim (fun _ : I => (0 : ZMod 2)) (fun _ : J => 1) (split k)) C
  intro k l he
  rcases hk : split k with i | j <;> rcases hl : split l with i' | j'
  all_goals simp_all [C]

end Froberg
