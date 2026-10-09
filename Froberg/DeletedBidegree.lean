module

public import Froberg.DeletedBidegreeRows
public import Froberg.RetainedSubspaceGrowth

@[expose] public section

/-! Appendix C.1: deleting any one bidegree leaves a fixed positive fraction
of the product dimension, uniformly over every homogeneous source subspace. -/
noncomputable section
namespace Froberg
open Finset Module MvPolynomial MonomialExpansion

/-- The deleted-bidegree dimension estimate, in an equivalent denominator-free
form. The first block is the smaller block in a balanced decomposition. -/
theorem exists_deleted_bidegree_growth_threshold (d e : ℕ) (hd : 0 < d) :
    ∃ m₀ : ℕ, ∀ (K : Type*) [Field K] (n : ℕ) (S : Finset (Fin n)),
      m₀ ≤ S.card → S.card ≤ Sᶜ.card → Sᶜ.card ≤ S.card + 1 →
      ∀ (U : Submodule K (Poly K n)), U ≤ Forms K n e → ∀ j : ℕ,
        2 * (n + (e + d) - 1).choose (e + d) * finrank K U ≤
          5 * (n + e - 1).choose e * finrank K
            ((U * Forms K n d).map (retainMonomials (fun a => partialDegree S a ≠ j))) := by
  obtain ⟨m₀, hm₀⟩ := exists_deleted_row_threshold hd e
  refine ⟨max 1 m₀, ?_⟩
  intro K _ n S hm hle hupper U hU j
  have hpos : 0 < S.card := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hm)
  have hcard : S.card ≤ n := by simpa using card_le_univ S
  have hn : 0 < n := hpos.trans_le hcard
  apply retained_homogeneous_subspace_growth hn (fun a => partialDegree S a ≠ j) 2 5
    (U := U) (hU := hU)
  intro α
  have h := hm₀ n S ((le_max_right _ _).trans hm) hle hupper α.val (degree_val α) j
  convert h using 1
  congr 1
  simp only [sum_filter]
  exact sum_coe_sort (exponents n (e + d))
    (fun β : Fin n →₀ ℕ => if partialDegree S β ≠ j then weight β α.val else 0)

/-- The exact degrees used in Appendix C.1. -/
theorem deleted_bidegree_lemma (d : ℕ) (hd : 2 ≤ d) :
    ∃ m₀ : ℕ, ∀ (K : Type*) [Field K] (n : ℕ) (S : Finset (Fin n)),
      m₀ ≤ S.card → S.card ≤ Sᶜ.card → Sᶜ.card ≤ S.card + 1 →
      ∀ (U : Submodule K (Poly K n)), U ≤ Forms K n (d - 2) → ∀ j : ℕ,
        2 * (n + (2 * d - 2) - 1).choose (2 * d - 2) * finrank K U ≤
          5 * (n + (d - 2) - 1).choose (d - 2) * finrank K
            ((U * Forms K n d).map (retainMonomials (fun a => partialDegree S a ≠ j))) := by
  simpa only [show d - 2 + d = 2 * d - 2 by omega] using
    exists_deleted_bidegree_growth_threshold d (d - 2) (by omega)

end Froberg
