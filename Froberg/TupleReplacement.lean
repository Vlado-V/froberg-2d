module

public import Froberg.CriticalChildFlag
public import Froberg.Hyperplane

@[expose] public section

/-! Literal one-slot replacement preserves the tuple's labels and is
independent whenever the additional vector is transverse to its old span. -/
noncomputable section
namespace Froberg
open Module
variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [DecidableEq I]

def puncturedTupleSpan (Q : I → V) (i : I) : Submodule K V :=
  Submodule.span K (Q '' {j | j≠i})

theorem tuple_update_span (Q : I → V) (i : I) (M : V) :
    Submodule.span K (Set.range (Function.update Q i M))=
      puncturedTupleSpan Q i ⊔ Submodule.span K {M} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    by_cases hj : j=i
    · subst j
      rw [Function.update_self]
      exact Submodule.mem_sup_right (Submodule.subset_span rfl)
    · rw [Function.update_of_ne hj]
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨j,hj,rfl⟩)
  · apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨j,hj,rfl⟩
      exact Submodule.subset_span ⟨j,Function.update_of_ne hj _ _⟩
    · apply Submodule.span_le.mpr
      rintro _ rfl
      exact Submodule.subset_span ⟨i,Function.update_self _ _ _⟩

theorem tuple_span_split (Q : I → V) (i : I) :
    Submodule.span K (Set.range Q)=puncturedTupleSpan Q i ⊔ Submodule.span K {Q i} := by
  simpa only [Function.update_eq_self] using tuple_update_span Q i (Q i)

theorem tuple_slot_not_mem_punctured (Q : I → V) (hQ : LinearIndependent K Q) (i : I) :
    Q i∉puncturedTupleSpan (K := K) Q i :=
  hQ.notMem_span_image (by simp)

theorem transverse_tuple_replacement_independent (Q : I → V) (hQ : LinearIndependent K Q)
    (i : I) (M : V) (hM : M∉Submodule.span K (Set.range Q)) (ε : K) :
    LinearIndependent K (Function.update Q i (Q i+ε • M)) := by
  classical
  let F : Option I → V := fun j => j.elim M Q
  have hF : LinearIndependent K F := by
    convert hQ.option hM using 1
    funext o
    cases o <;> rfl
  have hnew : LinearIndependent K (Function.update F (some i) (Q i+ε • M)) := by
    apply hF.update (some i) (Q i+ε • M)
    refine ⟨1,by simp,Finsupp.single (some i) 1+Finsupp.single none ε,by simp,?_⟩
    simp only [one_smul,map_add,Finsupp.linearCombination_single,F,Option.elim_some,Option.elim_none]
  have hh := hnew.comp (@Option.some I) (Option.some_injective I)
  have heq : (Function.update F (some i) (Q i+ε • M)) ∘ Option.some=
      Function.update Q i (Q i+ε • M) := by
    funext j
    by_cases hj : j=i
    · subst j
      simp
    · simp [Function.comp_def,Function.update_of_ne hj,F,hj]
  rwa [heq] at hh

end Froberg
