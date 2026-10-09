module

public import Froberg.Hyperplane

@[expose] public section

/-! The subspace hypotheses of exact replacement follow from independent
positive components modulo the scalar coefficient space. -/
noncomputable section
namespace Froberg
variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem span_disjoint_of_independent_quotient (A : Submodule K V) (g : I → V)
    (hg : LinearIndependent K (fun i => A.mkQ (g i))) :
    Disjoint (Submodule.span K (Set.range g)) A := by
  simpa only [Submodule.ker_mkQ] using
    (Submodule.range_ker_disjoint (f := A.mkQ) (v := g) hg)

theorem sum_inf_of_independent_quotient (A Q : Submodule K V) (hQ : Q≤A) (g : I → V)
    (hg : LinearIndependent K (fun i => A.mkQ (g i))) :
    (Q ⊔ Submodule.span K (Set.range g)) ⊓ A=Q := by
  rw [sup_inf_assoc_of_le _ hQ,(span_disjoint_of_independent_quotient A g hg).eq_bot,sup_bot_eq]

theorem extra_not_mem_of_independent_quotient (A : Submodule K V) (g : I → V) (M : V)
    (hg : LinearIndependent K (fun i : Option I => A.mkQ (i.elim M g))) :
    M∉Submodule.span K (Set.range g) ⊔ A := by
  intro hm
  have hm' : A.mkQ M∈(Submodule.span K (Set.range g) ⊔ A).map A.mkQ :=
    Submodule.mem_map_of_mem hm
  have himage : (fun i : Option I => A.mkQ (i.elim M g)) '' Set.range (@Option.some I)=
      Set.range (fun i => A.mkQ (g i)) := by
    rw [← Set.range_comp]
    rfl
  have hn := hg.notMem_span_image (s := Set.range (@Option.some I))
    (x := none) (by simp)
  rw [himage] at hn
  apply hn
  simpa only [Submodule.map_sup,Submodule.map_span,← Set.range_comp,
    Submodule.mkQ_map_self,sup_bot_eq,Function.comp_def,Option.elim_none] using hm'

theorem prepared_hyperplane_subspace_data
    (A Q Qminus B : Submodule K V) (f M : V)
    (hQA : Q≤A) (hQ : Q=Qminus ⊔ Submodule.span K {f})
    (hB : Disjoint B A) (hf : f∉Qminus) (hM : M∉B ⊔ A) :
    (Q ⊔ B) ⊓ A=Q ∧
    Q ⊔ B=(Qminus ⊔ B) ⊔ Submodule.span K {f} ∧
    Qminus≤Qminus ⊔ B ∧ f∉Qminus ⊔ B ∧ M∉(Q ⊔ B) ⊔ A := by
  have hQminus : Qminus≤A := (show Qminus≤Q by rw [hQ]; exact le_sup_left).trans hQA
  have hsmall : (Qminus ⊔ B) ⊓ A=Qminus := by
    rw [sup_inf_assoc_of_le _ hQminus,hB.eq_bot,sup_bot_eq]
  have hfA : f∈A := hQA (by rw [hQ]; exact Submodule.mem_sup_right (Submodule.subset_span rfl))
  refine ⟨?_,?_,le_sup_left,?_,?_⟩
  · rw [sup_inf_assoc_of_le _ hQA,hB.eq_bot,sup_bot_eq]
  · rw [hQ]
    ac_rfl
  · intro h
    apply hf
    have hh : f∈(Qminus ⊔ B) ⊓ A := ⟨h,hfA⟩
    rwa [hsmall] at hh
  · intro h
    apply hM
    exact (sup_le (sup_le (hQA.trans le_sup_right) le_sup_left) le_sup_right) h

end Froberg
