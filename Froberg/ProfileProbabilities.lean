module

public import Froberg.ProfileCapacityDrop

@[expose] public section

/-! Positivity and exact sums for the finite capacity distributions. -/
noncomputable section
namespace Froberg
open Finset MonomialExpansion

lemma profileAmbientCapacity_gt_one {s : ℕ} (hs : 0 < s) : 1 < profileAmbientCapacity s := by
  have hp := profileTargetCapacity_pos hs ⟨s, by omega⟩
  simpa [profileTargetCapacity, profileAmbientCapacity] using hp

lemma profileSourceCapacity_pos {H : ℝ} (hH : 1 < H) {s : ℕ} (i : Option (Fin s)) :
    0 < profileSourceCapacity H i := by
  cases i <;> simp only [profileSourceCapacity] <;> linarith

lemma finiteSourceProfile_pos {H : ℝ} {a z s : ℕ} (hH : 1 < H)
    (ha : 0 < a) (hz : 0 < z) (i : Option (Fin s)) : 0 < finiteSourceProfile H s a z i := by
  rw [finiteSourceProfile_eq_card]
  exact mul_pos (profileSourceCapacity_pos hH i) (by exact_mod_cast sourceMonomialFiber_card_pos ha hz i)

lemma finiteTargetProfile_pos {a z s : ℕ} (ha : 0 < a) (hz : 0 < z) (hs : 0 < s)
    (j : Fin (2*s+1)) : 0 < finiteTargetProfile s a z j := by
  rw [finiteTargetProfile_eq_card]
  exact mul_pos (profileTargetCapacity_pos hs j) (by exact_mod_cast targetMonomialFiber_card_pos ha hz j)

lemma finiteSourceProfile_total_pos {H : ℝ} {a z s : ℕ} (hH : 1 < H)
    (ha : 0 < a) (hz : 0 < z) : 0 < ∑ i, finiteSourceProfile H s a z i :=
  sum_pos (fun i _ => finiteSourceProfile_pos hH ha hz i) univ_nonempty

lemma finiteTargetProfile_total_pos {a z s : ℕ} (ha : 0 < a) (hz : 0 < z) (hs : 0 < s) :
    0 < ∑ j, finiteTargetProfile s a z j :=
  sum_pos (fun j _ => finiteTargetProfile_pos ha hz hs j) univ_nonempty

lemma normalized_weight_bounds {I : Type*} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 < w i) (i : I) : 0 < w i / ∑ k, w k ∧ w i / ∑ k, w k ≤ 1 := by
  have hsum : 0 < ∑ k, w k := (hw i).trans_le (single_le_sum (fun k _ => (hw k).le) (mem_univ i))
  exact ⟨div_pos (hw i) hsum, (div_le_one hsum).mpr (single_le_sum (fun k _ => (hw k).le) (mem_univ i))⟩

lemma sourceProfile_sum_atoms (H : ℝ) (a z s : ℕ) :
    (∑ α : Σ i, SourceMonomialFiber a z s i, profileSourceCapacity H α.1) =
      ∑ i, finiteSourceProfile H s a z i := by
  rw [Fintype.sum_sigma]
  simp only [sum_const, card_univ, nsmul_eq_mul, finiteSourceProfile_eq_card]
  apply sum_congr rfl
  intro i _
  ring

lemma targetProfile_sum_atoms (a z s : ℕ) :
    (∑ β : Σ j, TargetMonomialFiber a z s j, profileTargetCapacity s β.1) =
      ∑ j, finiteTargetProfile s a z j := by
  rw [Fintype.sum_sigma]
  simp only [sum_const, card_univ, nsmul_eq_mul, finiteTargetProfile_eq_card]
  apply sum_congr rfl
  intro i _
  ring

lemma normalized_source_atom {H : ℝ} {a z s : ℕ} (ha : 0 < a) (hz : 0 < z)
    (i : Option (Fin s)) :
    (finiteSourceProfile H s a z i / (∑ k, finiteSourceProfile H s a z k)) /
      (Fintype.card (SourceMonomialFiber a z s i) : ℝ) = sourceAtomMass H s a z i := by
  have hi : (Fintype.card (SourceMonomialFiber a z s i) : ℝ) ≠ 0 := by
    exact_mod_cast (sourceMonomialFiber_card_pos ha hz i).ne'
  rw [finiteSourceProfile_eq_card]
  unfold sourceAtomMass
  field_simp

lemma normalized_target_atom {a z s : ℕ} (ha : 0 < a) (hz : 0 < z) (j : Fin (2*s+1)) :
    (finiteTargetProfile s a z j / (∑ k, finiteTargetProfile s a z k)) /
      (Fintype.card (TargetMonomialFiber a z s j) : ℝ) = targetAtomMass s a z j := by
  have hj : (Fintype.card (TargetMonomialFiber a z s j) : ℝ) ≠ 0 := by
    exact_mod_cast (targetMonomialFiber_card_pos ha hz j).ne'
  rw [finiteTargetProfile_eq_card]
  unfold targetAtomMass
  field_simp

lemma monomialProfileJoint_pos_allowed {a z s : ℕ}
    (P : Option (Fin s) → Fin (2*s+1) → ℝ)
    (hPzero : ∀ i j, ¬profileAllowed i j → P i j = 0)
    (α : Σ i, SourceMonomialFiber a z s i) (β : Σ j, TargetMonomialFiber a z s j)
    (hp : 0 < monomialProfileJoint P α β) : profileAllowed α.1 β.1 := by
  by_contra hn
  have he : monomialProfileJoint P α β = 0 := by
    simp [monomialProfileJoint, fiberTransport, hPzero _ _ hn]
  linarith

end Froberg
