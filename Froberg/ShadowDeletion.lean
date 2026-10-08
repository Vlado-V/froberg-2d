import Froberg.ExceptionBudget

/-! Finite shadow bookkeeping after deleting a fixed collection of target
monomials. The loss is charged only to active source fibers. -/
noncomputable section
namespace Froberg.ShadowDeletion
open Finset
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def shadow (rel : I → J → Prop) [DecidableRel rel] (l : I → ℕ) (c : J → ℕ) (j : J) : ℕ :=
  univ.sup (fun i => if rel i j then min (l i) (c j) else 0)

lemma min_le_shadow (rel : I → J → Prop) [DecidableRel rel]
    (l : I → ℕ) (c : J → ℕ) (i : I) (j : J) (hij : rel i j) :
    min (l i) (c j) ≤ shadow rel l c j := by
  simpa only [shadow,ite_eq_left hij] using (le_sup (f := fun i => if rel i j then min (l i) (c j) else 0) (mem_univ i))

lemma shadow_le (rel : I → J → Prop) [DecidableRel rel]
    (l : I → ℕ) (c : J → ℕ) (j : J) : shadow rel l c j ≤ c j := by
  unfold shadow
  apply Finset.sup_le
  intro i _
  split_ifs
  · exact min_le_right _ _
  · exact Nat.zero_le _

lemma shadow_eq_zero_of_no_active (rel : I → J → Prop) [DecidableRel rel]
    (l : I → ℕ) (c : J → ℕ) (j : J)
    (hz : ∀ i, 0 < l i → ¬rel i j) : shadow rel l c j = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold shadow
  apply Finset.sup_le
  intro i _
  by_cases hi : 0 < l i
  · rw [if_neg (hz i hi)]
  · have hi0 : l i=0 := by omega
    simp [hi0]

lemma card_active_le (l : I → ℕ) : (univ.filter (fun i => 0 < l i)).card ≤ ∑ i,l i := by
  calc
    _ = ∑ i ∈ univ.filter (fun i => 0 < l i), 1 := by simp
    _ ≤ ∑ i ∈ univ.filter (fun i => 0 < l i), l i :=
      sum_le_sum (fun i hi => (mem_filter.mp hi).2)
    _ ≤ _ := sum_le_sum_of_subset (filter_subset _ _)

lemma discarded_shadow_le (rel : I → J → Prop) [DecidableRel rel]
    (l : I → ℕ) (c : J → ℕ) (B : Finset J) (C H : ℕ)
    (hc : ∀ j,c j ≤ H)
    (hC : ∀ i, 0 < l i → (B.filter (rel i)).card ≤ C) :
    (∑ j ∈ B, shadow rel l c j) ≤ H*C*(∑ i,l i) := by
  let P := univ.filter (fun i => 0 < l i)
  let E := P.biUnion (fun i => B.filter (rel i))
  have hE : E.card ≤ C*(∑ i,l i) := by
    calc
      E.card ≤ P.card*C := card_biUnion_le_card_mul P _ C (fun i hi => hC i (mem_filter.mp hi).2)
      _ ≤ (∑ i,l i)*C := Nat.mul_le_mul_right C (card_active_le l)
      _ = _ := Nat.mul_comm _ _
  have hp (j : J) (hj : j ∈ B) : shadow rel l c j ≤ if j ∈ E then H else 0 := by
    split_ifs with he
    · exact (shadow_le rel l c j).trans (hc j)
    · rw [shadow_eq_zero_of_no_active rel l c j]
      intro i hi hrel
      exact he (mem_biUnion.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩,mem_filter.mpr ⟨hj,hrel⟩⟩)
  have hsum := sum_le_sum hp
  have hEB : E ⊆ B := by
    intro j hj
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hj
    exact (mem_filter.mp hi).1
  have hi : ∑ j ∈ B, (if j ∈ E then H else 0) = E.card*H := by
    rw [← sum_filter]
    have he : B.filter (fun j => j ∈ E) = E := by ext j; simp only [mem_filter]; exact ⟨fun h => h.2,fun h => ⟨hEB h,h⟩⟩
    rw [he]
    simp
  rw [hi] at hsum
  nlinarith

lemma retained_shadow_bound (rel : I → J → Prop) [DecidableRel rel]
    (l : I → ℕ) (c : J → ℕ) (B : Finset J) (C H : ℕ)
    (hc : ∀ j,c j ≤ H)
    (hC : ∀ i, 0 < l i → (B.filter (rel i)).card ≤ C) :
    (∑ j,shadow rel l c j) ≤
      (∑ j ∈ univ\B,shadow rel l c j)+H*C*(∑ i,l i) := by
  have hsplit := sum_sdiff (subset_univ B) (f := shadow rel l c)
  have hl := discarded_shadow_le rel l c B C H hc hC
  omega

end Froberg.ShadowDeletion
