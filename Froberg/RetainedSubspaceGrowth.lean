module

public import Froberg.RetainedMonomials
public import Froberg.WeightedRetention
public import Froberg.MonomialExpansionBound
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex

@[expose] public section

/-! Weighted retained-row estimates pass from monomials to arbitrary homogeneous
subspaces by taking initial monomials. -/
noncomputable section
namespace Froberg
open Finset Module MvPolynomial MonomialExpansion
variable {K : Type*} [Field K] {n e d : ℕ}

theorem retained_homogeneous_subspace_growth (hn : 0 < n)
    (P : (Fin n →₀ ℕ) → Prop) [DecidablePred P] (a b : ℕ)
    (hrow : ∀ α : Degree n e,
      a * (n + e + d - 1).choose d ≤
        b * ∑ β ∈ (univ : Finset (Degree n (e + d))).filter (fun β => P β.val),
          weight β.val α.val)
    (U : Submodule K (Poly K n)) (hU : U ≤ Forms K n e) :
    a * (n + (e + d) - 1).choose (e + d) * finrank K U ≤
      b * (n + e - 1).choose e * finrank K ((U * Forms K n d).map (retainMonomials P)) := by
  classical
  let m : MonomialOrder (Fin n) := MonomialOrder.degLex
  let A : Finset (Degree n e) := univ.filter (fun α => α.val ∈ initialDegrees (d := e) m U)
  have hA : A.card = finrank K U := by
    rw [← card_initialDegrees m U hU]
    apply card_bij (fun α _ => α.val)
    · intro α hα
      exact (mem_filter.mp hα).2
    · intro α hα γ hγ heq
      exact Subtype.ext heq
    · intro α hα
      exact ⟨⟨α, mem_exponents.mpr (initialDegrees_degree m U hα)⟩,
        mem_filter.mpr ⟨mem_univ _, hα⟩, rfl⟩
  let T : Finset (Degree n (e + d)) := univ.filter (fun β => P β.val)
  let B := T.filter (fun β => ∃ α ∈ A, α.val ≤ β.val)
  have hsum (α : Degree n e) (hα : α ∈ A) :
      ∑ β ∈ B, weight β.val α.val = ∑ β ∈ T, weight β.val α.val := by
    apply sum_subset (filter_subset _ _)
    intro β hβ hβB
    apply Nat.eq_zero_of_not_pos
    intro hw
    exact hβB (mem_filter.mpr ⟨hβ, α, hα, (weight_pos_iff _ _).mp hw⟩)
  have hret : a * (n + e + d - 1).choose d * A.card ≤
      b * (e + d).choose e * B.card := by
    apply weighted_retention_bound (fun β α => weight β.val α.val) A B
    · intro α hα
      rw [hsum α hα]
      exact hrow α
    · intro β hβ
      rw [← weighted_row β]
      exact sum_le_sum_of_subset (subset_univ A)
  have htotal := weighted_total
    (fun (β : Degree n (e + d)) (α : Degree n e) => weight β.val α.val)
    ((e + d).choose e) ((n + e + d - 1).choose d) weighted_row (weighted_column hn)
  rw [card_degree, card_degree] at htotal
  have hnorm := normalized_retention_bound
    ((n + e - 1).choose e) ((n + (e + d) - 1).choose (e + d)) A.card B.card a b
    ((n + e + d - 1).choose d) ((e + d).choose e)
    (Nat.choose_pos (Nat.le_add_right _ _)) htotal hret
  let B' : Finset (Fin n →₀ ℕ) := B.image Subtype.val
  have hBcard : B'.card = B.card := card_image_iff.mpr (fun _ _ _ _ h => Subtype.ext h)
  have hB : B.card ≤ finrank K ((U * Forms K n d).map (retainMonomials P)) := by
    rw [← hBcard]
    apply card_le_finrank_retained_product_of_initial_factors m P U hU B'
    · intro β hβ
      obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hβ
      exact (mem_filter.mp (mem_filter.mp hγ).1).2
    · intro β hβ
      obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hβ
      obtain ⟨α, hα, hαγ⟩ := (mem_filter.mp hγ).2
      refine ⟨α.val, (mem_filter.mp hα).2, γ.val - α.val, ?_, add_tsub_cancel_of_le hαγ⟩
      have h := congrArg Finsupp.degree (tsub_add_cancel_of_le hαγ)
      rw [map_add, degree_val, degree_val] at h
      omega
  rw [hA] at hnorm
  exact hnorm.trans (Nat.mul_le_mul_left _ hB)

end Froberg
