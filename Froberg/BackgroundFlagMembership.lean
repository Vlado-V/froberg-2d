module

public import Froberg.BackgroundFlagSpan

@[expose] public section

/-! The even generators of the canonical replaced tuple belong to its
literal retained background, as required by the local comparison. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type} [Field K] [Infinite K]

section General
variable {U V I : Type*} [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
variable {q : ℕ}

theorem updated_scalar_mem_replaced_background (j : U →ₗ[K] V)
    (Q : Fin q → U) (hq : 0 < q) (b : I → V) (M : V) (c : K) (i : Fin q) :
    Function.update (fun i => j (Q i)) (lastScalarSlot hq)
      (j (Q (lastScalarSlot hq))+c • M) i∈replacedFlagBackground j Q hq b M c := by
  have hle : Submodule.span K (Set.range (Function.update (fun i => j (Q i))
      (lastScalarSlot hq) (j (Q (lastScalarSlot hq))+c • M)))≤
      replacedFlagBackground j Q hq b M c := by
    rw [mapped_scalar_flag_update_span]
    exact sup_le (le_sup_of_le_left le_sup_left) le_sup_right
  exact hle (Submodule.subset_span ⟨i,rfl⟩)
end General

variable {h m d q f u e : ℕ}

theorem background_replaced_even_mem
    (Q : Fin q → Forms K m d) (hq : 0 < q)
    (E : Fin e → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (M : biformParitySpace K h m d 0) (c : K)
    (i : Fin (Fintype.card (BackgroundLabel (q+e) f u)))
    (hi : indexedSplitParity (backgroundSplitIndex (q := q+e) (f := f) (u := u)) i=0) :
    backgroundEnumeratedForms
      (Fin.append (Function.update (fun i => scalarEvenBiform (h := h) (Q i))
        (lastScalarSlot hq) (scalarEvenBiform (Q (lastScalarSlot hq))+c • M)) E) F G i∈
      replacedFlagBackground (renameForm (Fin.natAdd h)) Q hq
        (backgroundPositiveForms E G) (evenPolynomialToForms M) c := by
  classical
  apply background_even_mem_of _ F G _ ?_ i hi
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro k
    rw [Fin.append_left]
    have hk := updated_scalar_mem_replaced_background (renameForm (Fin.natAdd h)) Q hq
      (backgroundPositiveForms E G) (evenPolynomialToForms M) c k
    by_cases he : k=lastScalarSlot hq
    · subst k
      simpa only [Function.update_self,map_add,map_smul,evenPolynomialToForms_scalar] using hk
    · simpa only [Function.update_of_ne he,evenPolynomialToForms_scalar] using hk
  · intro k
    rw [Fin.append_right]
    exact Submodule.mem_sup_left (Submodule.mem_sup_right
      (Submodule.subset_span ⟨Sum.inl k,rfl⟩))

end Froberg
