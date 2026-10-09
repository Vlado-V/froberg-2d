module

public import Froberg.GenericFlagOpen
public import Froberg.SupportedTargetDeletion
public import Froberg.MonomialCounts

@[expose] public section

/-! The distinguished scalar slot and its codimension-one child flag are
literal prefix tuples. Deletion uses the full upper-count tuple and remains
injective on the smaller child image. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {q : ℕ}

def lastScalarSlot (hq : 0 < q) : Fin q := ⟨q-1,by omega⟩

def scalarFlagPrefix (Q : Fin q → V) : Fin (q-1) → V :=
  Q ∘ Fin.castLE (Nat.sub_le q 1)

theorem scalarFlagPrefix_independent (Q : Fin q → V) (hQ : LinearIndependent K Q) :
    LinearIndependent K (scalarFlagPrefix Q) :=
  hQ.comp _ (Fin.castLE_injective _)

theorem scalarFlag_span (hq : 0 < q) (Q : Fin q → V) :
    Submodule.span K (Set.range Q)=
      Submodule.span K (Set.range (scalarFlagPrefix Q)) ⊔
        Submodule.span K {Q (lastScalarSlot hq)} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    by_cases hi : i.val<q-1
    · apply Submodule.mem_sup_left
      exact Submodule.subset_span ⟨⟨i.val,hi⟩,congrArg Q (Fin.ext rfl)⟩
    · have he : i=lastScalarSlot hq := Fin.ext (by have := i.isLt; dsimp [lastScalarSlot];omega)
      rw [he]
      exact Submodule.mem_sup_right (Submodule.subset_span rfl)
  · apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Submodule.subset_span ⟨_,rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ rfl
      exact Submodule.subset_span ⟨_,rfl⟩

theorem scalarFlag_last_not_mem (hq : 0 < q) (Q : Fin q → V)
    (hQ : LinearIndependent K Q) :
    Q (lastScalarSlot hq)∉Submodule.span K (Set.range (scalarFlagPrefix Q)) := by
  have hn : lastScalarSlot hq∉Set.range (Fin.castLE (Nat.sub_le q 1)) := by
    rintro ⟨i,hi⟩
    have hv := congrArg Fin.val hi
    have := i.isLt
    change i.val=q-1 at hv
    omega
  have hh := hQ.notMem_span_image (s := Set.range (Fin.castLE (Nat.sub_le q 1))) hn
  simpa only [←Set.range_comp,scalarFlagPrefix] using hh

variable {n d r : ℕ}

theorem endpoint_prefix_range_le (Q : Fin q → Forms K n d) (hrs : r ≤ q) :
    (endpointMultiplication (Q ∘ Fin.castLE hrs)).range≤(endpointMultiplication Q).range := by
  rw [range_endpointMultiplication,range_endpointMultiplication]
  apply endpointProducts_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact Submodule.subset_span ⟨_,rfl⟩

variable [Infinite K]

theorem critical_child_flag_principal_open (hn : 0 < n) (d : ℕ) :
    ∃ D : MvPolynomial (CoefficientIndex n d (upperCount n d)) K,
      (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 →
        let Q := coefficientForms K n d (upperCount n d) a
        LinearIndependent K Q ∧
        LinearIndependent K (scalarFlagPrefix Q) ∧
        coefficientCokernel K n d (upperCount n d) a=genericCokernel K n d (upperCount n d) ∧
        finrank K (EndpointHomology (scalarFlagPrefix Q))=genericHomology K n d (upperCount n d-1) ∧
        Submodule.span K (Set.range Q)=Submodule.span K (Set.range (scalarFlagPrefix Q)) ⊔
          Submodule.span K {Q (lastScalarSlot (upperCount_pos hn d))} ∧
        Q (lastScalarSlot (upperCount_pos hn d))∉Submodule.span K (Set.range (scalarFlagPrefix Q)) := by
  obtain ⟨D,hD,hgood⟩ := generic_flag_principal_open (K := K) hn
    (Nat.sub_le (upperCount n d) 1) (upperCount_le_monomial_count hn d)
  refine ⟨D,hD,?_⟩
  intro a ha
  have hh := hgood a ha
  exact ⟨hh.1,scalarFlagPrefix_independent _ hh.1,hh.2.1,hh.2.2.2,
    scalarFlag_span (upperCount_pos hn d) _,scalarFlag_last_not_mem (upperCount_pos hn d) _ hh.1⟩

end Froberg
