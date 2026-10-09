module

public import Froberg.QuarticBlockData

@[expose] public section

/-! Every quartic product fiber can be relabeled so that its doubled indices
come first, followed by its single indices. -/
noncomputable section
namespace Froberg.QuarticBlocks
open Finset
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem card_initialSet {k : ℕ} (hk : k ≤ 8) : (initialSet k).card = k := by
  interval_cases k <;> decide +kernel

/-- The relabeling is an embedding into the fixed eight-vertex certificate,
with both relevant finite subsets mapped exactly, not merely cardinalities. -/
theorem exists_normalizing_embedding (I : Finset X) (r : Fin 5)
    (hcard : Fintype.card X = 8-r.val) (hI : I.card = r.val) :
    ∃ e : X ↪ Fin 8, I.map e = initialSet r.val ∧
      (Finset.univ : Finset X).map e = initialSet (8-r.val) := by
  classical
  let ei : I ≃ Fin r.val := Fintype.equivFinOfCardEq (by simpa using hI)
  have hIc : Fintype.card ↥Iᶜ = 8-2*r.val := by
    rw [Fintype.card_coe, card_compl, hcard, hI]
    omega
  let er : ↥Iᶜ ≃ Fin (8-2*r.val) := Fintype.equivFinOfCardEq hIc
  let f : X → Fin 8 := fun x =>
    if hx : x ∈ I then ⟨(ei ⟨x,hx⟩).val, by have := (ei ⟨x,hx⟩).isLt; omega⟩
    else ⟨r.val + (er ⟨x,mem_compl.mpr hx⟩).val,
      by have := (er ⟨x,mem_compl.mpr hx⟩).isLt; omega⟩
  have hf : Function.Injective f := by
    intro x y h
    have hv := congrArg Fin.val h
    by_cases hx : x ∈ I <;> by_cases hy : y ∈ I
    · have he : ei ⟨x,hx⟩ = ei ⟨y,hy⟩ := Fin.ext (by simpa only [f,dif_pos hx,dif_pos hy] using hv)
      exact congrArg Subtype.val (ei.injective he)
    · have hl := (ei ⟨x,hx⟩).isLt
      simp only [f,dif_pos hx,dif_neg hy] at hv
      omega
    · have hl := (ei ⟨y,hy⟩).isLt
      simp only [f,dif_neg hx,dif_pos hy] at hv
      omega
    · have he : er ⟨x,mem_compl.mpr hx⟩ = er ⟨y,mem_compl.mpr hy⟩ := by
        apply Fin.ext
        simp only [f,dif_neg hx,dif_neg hy] at hv
        omega
      exact congrArg Subtype.val (er.injective he)
  let e : X ↪ Fin 8 := ⟨f,hf⟩
  refine ⟨e, ?_, ?_⟩
  · apply eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := mem_map.mp hy
      simp only [initialSet, mem_filter, mem_univ, true_and]
      change (f x).val < r.val
      simpa only [f,dif_pos hx] using (ei ⟨x,hx⟩).isLt
    · rw [card_map,hI,card_initialSet (by omega)]
  · apply eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := mem_map.mp hy
      simp only [initialSet, mem_filter, mem_univ, true_and]
      change (f x).val < 8-r.val
      by_cases hx : x ∈ I
      · have hl := (ei ⟨x,hx⟩).isLt
        simp only [f,dif_pos hx]
        omega
      · have hl := (er ⟨x,mem_compl.mpr hx⟩).isLt
        simp only [f,dif_neg hx]
        omega
    · rw [card_map,card_univ,hcard,card_initialSet (by omega)]

end Froberg.QuarticBlocks
