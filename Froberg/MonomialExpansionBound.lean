module

public import Froberg.MonomialShadow
public import Froberg.WeightedExpansion

@[expose] public section

/-! An explicit eventual expansion bound, uniform over all monomial sets. -/
noncomputable section
namespace Froberg.MonomialExpansion
open Finset

theorem weighted_row {n e d : ℕ} (b : Degree n (e + d)) :
    ∑ a : Degree n e, weight b.val a.val = (e + d).choose e := by
  rw [Finset.sum_coe_sort]
  simpa only [degree_val] using sum_weight_sources b.val e

theorem weighted_column {n e d : ℕ} (hn : 0 < n) (a : Degree n e) :
    ∑ b : Degree n (e + d), weight b.val a.val = (n + e + d - 1).choose d := by
  have h := sum_weight_targets hn a.val d
  rw [degree_val] at h
  calc
    (∑ b : Degree n (e + d), weight b.val a.val) =
        ∑ b ∈ exponents n (e + d), weight b a.val :=
          Finset.sum_coe_sort (exponents n (e + d)) (fun b : Fin n →₀ ℕ => weight b a.val)
    _ = _ := h

theorem weighted_shadow_cut {n e d : ℕ} (hn : 0 < n) (A : Finset (Degree n e)) :
    (n + e + d - 1).choose d * A.card + (mixed d A).card ≤
      (e + d).choose e * (shadow d A).card := by
  apply Froberg.weighted_cut_bound (fun b a => weight b.val a.val)
    A (shadow d A) (mixed d A) ((e + d).choose e) ((n + e + d - 1).choose d)
    weighted_row (weighted_column hn)
  · intro b hb a ha
    apply Nat.eq_zero_of_not_pos
    intro hp
    apply hb
    exact mem_filter.mpr ⟨mem_univ b, a, ha, (weight_pos_iff _ _).mp hp⟩
  · exact filter_subset _ _
  · intro b hb
    obtain ⟨a, ha, hab⟩ := (mem_filter.mp hb).2
    rw [← weighted_row b]
    exact sum_lt_sum_of_subset (subset_univ A) (mem_univ a) ha
      ((weight_pos_iff _ _).mpr hab) (fun _ _ _ => Nat.zero_le _)

/-- Once the number of extra factors exceeds an explicit degree-only constant,
every monomial shadow has the strengthened normalized growth needed for generic
maximal rank below twice the generating degree. -/
theorem shadow_expansion {n e d : ℕ} (hn : 0 < n) (hed : e ≤ d)
    (hlarge : (e + d).choose e * ((e + d).choose e * d.choose e) ≤
      (n + (d - e) - 1).choose (d - e)) (A : Finset (Degree n e)) :
    (n + (e + d) - 1).choose (e + d) * A.card +
      (n + e - 1).choose e * A.card * ((n + e - 1).choose e - A.card) ≤
      (n + e - 1).choose e * (shadow d A).card := by
  have htotal := Froberg.weighted_total
    (fun (b : Degree n (e + d)) (a : Degree n e) => weight b.val a.val)
    ((e + d).choose e) ((n + e + d - 1).choose d) weighted_row (weighted_column hn)
  have hC : 0 < (e + d).choose e := Nat.choose_pos (Nat.le_add_right _ _)
  have hB : 0 < (e + d).choose e * d.choose e := Nat.mul_pos hC (Nat.choose_pos hed)
  have h := Froberg.strengthened_weighted_expansion
    (Fintype.card (Degree n e)) (Fintype.card (Degree n (e + d))) A.card
    (shadow d A).card (mixed d A).card ((e + d).choose e)
    ((n + e + d - 1).choose d) ((e + d).choose e * d.choose e)
    ((n + (d - e) - 1).choose (d - e)) hC hB htotal (weighted_shadow_cut hn A)
    (by simpa only [card_degree] using triple_count_le_mixed hed A) hlarge
  simpa only [card_degree] using h

/-- The pure powers give at least one degree-`k` monomial per variable. -/
theorem variables_le_monomials (n k : ℕ) (hk : 0 < k) :
    n ≤ (n + k - 1).choose k := by
  let f : Fin n ↪ Degree n k :=
    ⟨fun i => ⟨Finsupp.single i k, mem_exponents.mpr (by simp)⟩,
      fun i j h => Finsupp.single_left_injective hk.ne' (congrArg Subtype.val h)⟩
  simpa only [Fintype.card_fin, card_degree] using Fintype.card_le_of_embedding f

/-- An explicit variable-count threshold suffices for all source subsets. -/
theorem shadow_expansion_of_large_variables {n e d : ℕ} (hn : 0 < n) (hed : e < d)
    (hlarge : (e + d).choose e * ((e + d).choose e * d.choose e) ≤ n)
    (A : Finset (Degree n e)) :
    (n + (e + d) - 1).choose (e + d) * A.card +
      (n + e - 1).choose e * A.card * ((n + e - 1).choose e - A.card) ≤
      (n + e - 1).choose e * (shadow d A).card :=
  shadow_expansion hn hed.le
    (hlarge.trans (variables_le_monomials n (d - e) (Nat.sub_pos_of_lt hed))) A

/-- Uniform eventual strengthened growth; there is no asymptotic hypothesis. -/
theorem exists_shadow_expansion_threshold (e d : ℕ) (hed : e < d) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ A : Finset (Degree n e),
      (n + (e + d) - 1).choose (e + d) * A.card +
        (n + e - 1).choose e * A.card * ((n + e - 1).choose e - A.card) ≤
        (n + e - 1).choose e * (shadow d A).card := by
  refine ⟨max 1 ((e + d).choose e * ((e + d).choose e * d.choose e)), ?_⟩
  intro n hn A
  exact shadow_expansion_of_large_variables
    (lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hn)) hed
    ((le_max_right _ _).trans hn) A

end Froberg.MonomialExpansion
