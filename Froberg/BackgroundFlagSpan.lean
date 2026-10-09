module

public import Froberg.ReplacementEnumeration
public import Froberg.OddExactEnumeration
public import Froberg.FlagReplacement
public import Froberg.OddEndpointScalarSlices
public import Froberg.OddEvenExtension

@[expose] public section

/-! Literal canonical generator spans before and after the scalar flag
replacement. The positive background uses exactly the even-layer and
private odd labels; the full outer family remains separate. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u e : ℕ}

def oddPolynomialToForms : biformParitySpace K h m d 1 →ₗ[K] Forms K (h+m) d :=
  (parityPartForms ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm) 1).subtype.comp
    (parityPolynomialToFormsEquiv finSumFinEquiv
      (fun i => (blockWeight h m i : ZMod 2)) 1).toLinearMap

@[simp] theorem oddPolynomialToForms_val (a : biformParitySpace K h m d 1) :
    (oddPolynomialToForms a).val=rename finSumFinEquiv a.val := rfl

theorem backgroundEnumeratedForms_reindex
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1) :
    backgroundEnumeratedForms Q F G ∘ (Fintype.equivFin (BackgroundLabel q f u))=
      Sum.elim (fun i => evenPolynomialToForms (Q i))
        (Sum.elim (fun i => oddPolynomialToForms (F i)) (fun i => oddPolynomialToForms (G i))) := by
  funext i
  apply Subtype.ext
  change rename finSumFinEquiv
    (backgroundParityFamily Q F G ((Fintype.equivFin _).symm ((Fintype.equivFin _) i))).val=_
  rw [Equiv.symm_apply_apply]
  rcases i with i | (i | i) <;> rfl

theorem backgroundEnumeratedForms_span
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1) :
    Submodule.span K (Set.range (backgroundEnumeratedForms Q F G))=
      Submodule.span K (Set.range (fun i => evenPolynomialToForms (Q i))) ⊔
        (Submodule.span K (Set.range (fun i => oddPolynomialToForms (F i))) ⊔
          Submodule.span K (Set.range (fun i => oddPolynomialToForms (G i)))) := by
  rw [←(Fintype.equivFin (BackgroundLabel q f u)).surjective.range_comp
    (backgroundEnumeratedForms Q F G),backgroundEnumeratedForms_reindex,
    Set.Sum.elim_range,Set.Sum.elim_range,Submodule.span_union,Submodule.span_union]

theorem background_even_mem_of
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (T : Submodule K (Forms K (h+m) d))
    (hQ : ∀ i,evenPolynomialToForms (Q i)∈T)
    (i : Fin (Fintype.card (BackgroundLabel q f u)))
    (hi : indexedSplitParity (backgroundSplitIndex (q := q) (f := f) (u := u)) i=0) :
    backgroundEnumeratedForms Q F G i∈T := by
  rw [background_split_parity_eq] at hi
  obtain ⟨j,rfl⟩ := (Fintype.equivFin (BackgroundLabel q f u)).surjective i
  simp only [Function.comp_apply,Equiv.symm_apply_apply] at hi
  rcases j with j | (j | j)
  · rw [←backgroundEvenIndex,backgroundEnumeratedForms_even]
    exact hQ j
  · exact (one_ne_zero hi).elim
  · exact (one_ne_zero hi).elim

def backgroundPositiveForms
    (E : Fin e → biformParitySpace K h m d 0)
    (G : Fin u → biformParitySpace K h m d 1) : Fin e ⊕ Fin u → Forms K (h+m) d :=
  Sum.elim (fun i => evenPolynomialToForms (E i)) (fun i => oddPolynomialToForms (G i))

theorem evenPolynomialToForms_scalar (a : Forms K m d) :
    evenPolynomialToForms (scalarEvenBiform (h := h) a)=renameForm (Fin.natAdd h) a := by
  apply Subtype.ext
  rw [evenPolynomialToForms_val,scalarEvenBiform_val]
  change rename finSumFinEquiv (rename Sum.inr a.val)=rename (Fin.natAdd h) a.val
  rw [rename_rename]
  rfl

section GeneralFlag
variable {U V : Type*} [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]

theorem scalarFlagPrefix_update_last (Q : Fin q → V) (hq : 0 < q) (M : V) :
    scalarFlagPrefix (Function.update Q (lastScalarSlot hq) M)=scalarFlagPrefix Q := by
  classical
  funext i
  apply Function.update_of_ne
  intro he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  change i.val=q-1 at hv
  omega

theorem mapped_scalar_flag_update_span (j : U →ₗ[K] V) (Q : Fin q → U)
    (hq : 0 < q) (M : V) :
    Submodule.span K (Set.range (Function.update (fun i => j (Q i)) (lastScalarSlot hq) M))=
      embeddedFlagSpace j (scalarFlagPrefix Q) ⊔ Submodule.span K {M} := by
  rw [scalarFlag_span hq,scalarFlagPrefix_update_last,Function.update_self]
  congr 1
  rw [embeddedFlagSpace,Submodule.map_span,←Set.range_comp]
  rfl

end GeneralFlag

private theorem background_sup_reorder {α : Type*} [SemilatticeSup α]
    (A B C D E : α) : ((A ⊔ B) ⊔ C) ⊔ (D ⊔ E)=((A ⊔ (C ⊔ E)) ⊔ B) ⊔ D := by
  ac_rfl

theorem background_replaced_flag_span
    (Q : Fin q → Forms K m d) (hq : 0 < q)
    (E : Fin e → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (M : biformParitySpace K h m d 0) (c : K) :
    Submodule.span K (Set.range (backgroundEnumeratedForms
      (Fin.append (Function.update (fun i => scalarEvenBiform (h := h) (Q i))
        (lastScalarSlot hq) (scalarEvenBiform (Q (lastScalarSlot hq))+c • M)) E) F G))=
      replacedFlagBackground (renameForm (Fin.natAdd h)) Q hq
        (backgroundPositiveForms E G) (evenPolynomialToForms M) c ⊔
          Submodule.span K (Set.range (fun i => oddPolynomialToForms (F i))) := by
  classical
  let S : Fin q → biformParitySpace K h m d 0 := fun i => scalarEvenBiform (Q i)
  let S' := Function.update S (lastScalarSlot hq) (S (lastScalarSlot hq)+c • M)
  have hmap : (fun i => evenPolynomialToForms (S' i))=
      Function.update (fun i => renameForm (Fin.natAdd h) (Q i)) (lastScalarSlot hq)
        (renameForm (Fin.natAdd h) (Q (lastScalarSlot hq))+c • evenPolynomialToForms M) := by
    funext i
    by_cases hi : i=lastScalarSlot hq
    · subst i
      simp only [S',Function.update_self,map_add,map_smul,S,evenPolynomialToForms_scalar]
    · simp only [S',Function.update_of_ne hi,S,evenPolynomialToForms_scalar]
  have happ : (fun i => evenPolynomialToForms (Fin.append S' E i))=
      Fin.append (fun i => evenPolynomialToForms (S' i)) (fun i => evenPolynomialToForms (E i)) := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp only [Fin.append_left,Fin.append_right]
  change Submodule.span K (Set.range (backgroundEnumeratedForms (Fin.append S' E) F G))=_
  rw [backgroundEnumeratedForms_span,happ,span_fin_append,hmap,mapped_scalar_flag_update_span]
  unfold replacedFlagBackground backgroundPositiveForms
  rw [Set.Sum.elim_range,Submodule.span_union]
  exact background_sup_reorder _ _ _ _ _

end Froberg
