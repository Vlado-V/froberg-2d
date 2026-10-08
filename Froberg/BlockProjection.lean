import Froberg.MixedPacking
import Froberg.ProjectionFailure

/-! Actual quotient-projection failures for blocks of attached relations. -/
noncomputable section
namespace Froberg.MixedExterior
open Module
variable {K α : Type*} [Field K] [DecidableEq α] {h : ℕ}

@[simp] theorem blockSpan_empty (v : α → Fin h → K) : blockSpan v ∅ = ⊥ := by
  have heq : v '' ((∅ : Finset α) : Set α) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨y,hy,rfl⟩
    exact Finset.notMem_empty y hy
  rw [blockSpan,heq,Submodule.span_empty]

theorem blockSpan_mono (v : α → Fin h → K) {S T : Finset α} (hST : S ⊆ T) :
    blockSpan v S ≤ blockSpan v T :=
  Submodule.span_mono (Set.image_mono hST)

theorem blockSpan_union (v : α → Fin h → K) (S T : Finset α) :
    blockSpan v (S ∪ T) = blockSpan v S ⊔ blockSpan v T := by
  simp [blockSpan,Set.image_union,Submodule.span_union]

theorem blockSpan_finrank (v : α → Fin h → K) (S : Finset α)
    (hi : LinearIndependent K (fun i : S => v i.val)) :
    finrank K (blockSpan v S) = S.card := by
  have he : v '' (S : Set α) = Set.range (fun i : S => v i.val) := by
    ext x
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.property,rfl⟩
  rw [blockSpan,he]
  simpa using finrank_span_eq_card hi

/-- The exact failure implication for a source relation block contained in a
target relation block, applied to an arbitrary lifted source subspace. -/
theorem deficient_block_projection {v : α → Fin h → K} {S T : Finset α}
    (hST : S ⊆ T)
    (hiS : LinearIndependent K (fun i : S => v i.val))
    (hiT : LinearIndependent K (fun i : T => v i.val))
    (U : Submodule K (Fin h → K)) (hSU : blockSpan v S ≤ U)
    (hf : finrank K (U.map (blockSpan v T).mkQ) <
      min (finrank K (U.map (blockSpan v S).mkQ))
        (finrank K ((Fin h → K) ⧸ blockSpan v T))) :
    finrank K ↥(U ⊔ blockSpan v (T \ S)) <
      min (finrank K U + (T \ S).card) h := by
  have he : blockSpan v S ⊔ blockSpan v (T \ S) = blockSpan v T := by
    rw [← blockSpan_union,Finset.union_sdiff_of_subset hST]
  have heU : U ⊔ blockSpan v T = U ⊔ blockSpan v (T \ S) := by
    rw [← he,← sup_assoc,sup_eq_left.mpr hSU]
  have hS := blockSpan_finrank v S hiS
  have hT := blockSpan_finrank v T hiT
  have hsource := Quartic.QuotientBilinearImage.finrank_map_mkQ_add (blockSpan v S) U hSU
  have htarget := (blockSpan v T).finrank_quotient_add_finrank
  have himage := ProjectionFailure.image_finrank_add U (blockSpan v T)
  have hcard := Finset.card_sdiff_add_card_eq_card hST
  rw [hS] at hsource
  rw [hT] at htarget himage
  rw [heU] at himage
  simp only [Module.finrank_pi_fintype,Module.finrank_self,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at htarget
  omega

end Froberg.MixedExterior
