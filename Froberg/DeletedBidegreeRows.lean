module

public import Froberg.SplitWeights
public import Froberg.BalancedWeightPolynomial

@[expose] public section

/-! A uniform weighted bound for deleting one bidegree in a balanced split. -/
noncomputable section
namespace Froberg.MonomialExpansion
open Finset Filter
open scoped Topology

theorem deleted_row_bound_of_count_bounds {n d e : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (a : Fin n →₀ ℕ) (ha : a.degree = e)
    (hcounts : ∀ u ≤ d,
      5 * ((S.card + partialDegree S a + u - 1).choose u *
        (Sᶜ.card + (e - partialDegree S a) + (d - u) - 1).choose (d - u)) ≤
      3 * (n + e + d - 1).choose d) (j : ℕ) :
    5 * (∑ b ∈ (exponents n (e + d)).filter (fun b => partialDegree S b = j), weight b a) ≤
      3 * (n + e + d - 1).choose d := by
  by_cases hex : ∃ u ≤ d, j = partialDegree S a + u
  · obtain ⟨u, hu, rfl⟩ := hex
    have hc : partialDegree Sᶜ a = e - partialDegree S a := by
      have h := partialDegree_add_compl S a
      rw [ha] at h
      omega
    have h := sum_weight_target_bidegree S hS hSc a u (d - u)
    rw [Nat.add_sub_of_le hu, ha, hc] at h
    rw [h]
    exact hcounts u hu
  · have hz : ∑ b ∈ (exponents n (e + d)).filter (fun b => partialDegree S b = j),
        weight b a = 0 := by
      apply sum_eq_zero
      intro b hb
      obtain ⟨hbdeg, hbj⟩ := mem_filter.mp hb
      by_contra hw
      obtain ⟨u, hu, hju⟩ := target_bidegree_possible S a b
        (by simpa only [ha] using mem_exponents.mp hbdeg) hw
      exact hex ⟨u, hu, hbj.symm.trans hju⟩
    simp [hz]

theorem retained_row_bound_of_deleted_bound {n d e : ℕ} (hn : 0 < n)
    (S : Finset (Fin n)) (a : Fin n →₀ ℕ) (ha : a.degree = e) (j : ℕ)
    (hdel : 5 * (∑ b ∈ (exponents n (e + d)).filter (fun b => partialDegree S b = j),
      weight b a) ≤ 3 * (n + e + d - 1).choose d) :
    2 * (n + e + d - 1).choose d ≤
      5 * (∑ b ∈ (exponents n (e + d)).filter (fun b => partialDegree S b ≠ j), weight b a) := by
  have hsum := sum_filter_add_sum_filter_not (exponents n (e + d))
    (fun b => partialDegree S b = j) (fun b => weight b a)
  have htotal := sum_weight_targets hn a d
  rw [ha] at htotal
  rw [htotal] at hsum
  change (∑ b ∈ (exponents n (e + d)).filter (fun b => partialDegree S b = j), weight b a) +
    (∑ b ∈ (exponents n (e + d)).filter (fun b => partialDegree S b ≠ j), weight b a) =
      (n + e + d - 1).choose d at hsum
  omega

/-- The count bounds hold simultaneously for all source and extension bidegrees,
and for either parity of the ambient dimension. -/
theorem eventually_balanced_count_bounds {d : ℕ} (hd : 0 < d) (e : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ i ≤ e, ∀ u ≤ d, ∀ ε ≤ 1,
      5 * ((m + i + u - 1).choose u *
        (m + ε + (e - i) + (d - u) - 1).choose (d - u)) ≤
      3 * (2 * m + ε + e + d - 1).choose d := by
  have h : ∀ᶠ m : ℕ in atTop, ∀ i : Fin (e + 1), ∀ u : Fin (d + 1), ∀ ε : Fin 2,
      5 * ((m + i.val + u.val - 1).choose u.val *
        (m + ε.val + (e - i.val) + (d - u.val) - 1).choose (d - u.val)) ≤
      3 * (2 * m + ε.val + e + d - 1).choose d := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro u
    apply eventually_all.mpr
    intro ε
    have h := Froberg.eventually_balanced_weight_bound hd
      (show u.val + (d - u.val) = d by omega) i.val (ε.val + (e - i.val)) (ε.val + e)
    simpa only [Nat.add_assoc] using h
  filter_upwards [h] with m hm
  intro i hi u hu ε hε
  exact hm ⟨i, by omega⟩ ⟨u, by omega⟩ ⟨ε, by omega⟩

/-- One bound works for all source monomials and all target bidegrees. -/
theorem exists_deleted_row_threshold {d : ℕ} (hd : 0 < d) (e : ℕ) :
    ∃ m₀ : ℕ, ∀ (n : ℕ) (S : Finset (Fin n)),
      m₀ ≤ S.card → S.card ≤ Sᶜ.card → Sᶜ.card ≤ S.card + 1 →
      ∀ (a : Fin n →₀ ℕ), a.degree = e → ∀ j : ℕ,
        2 * (n + e + d - 1).choose d ≤
          5 * (∑ b ∈ (exponents n (e + d)).filter (fun b => partialDegree S b ≠ j), weight b a) := by
  obtain ⟨m₁, hm₁⟩ := eventually_atTop.mp (eventually_balanced_count_bounds hd e)
  refine ⟨max 1 m₁, ?_⟩
  intro n S hm hle hupper a ha j
  have hpos : 0 < S.card := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hm)
  have hS : S.Nonempty := card_pos.mp hpos
  have hSc : Sᶜ.Nonempty := card_pos.mp (hpos.trans_le hle)
  let ε := Sᶜ.card - S.card
  have hε : ε ≤ 1 := by dsimp [ε]; omega
  have hsplit : Sᶜ.card = S.card + ε := by dsimp [ε]; omega
  have hcard : S.card + Sᶜ.card = n := by simpa using card_add_card_compl S
  have hn : 0 < n := by omega
  have hn' : n = 2 * S.card + ε := by omega
  have hi : partialDegree S a ≤ e := ha ▸ partialDegree_le_degree S a
  have hbound := hm₁ S.card ((le_max_right _ _).trans hm) (partialDegree S a) hi
  apply retained_row_bound_of_deleted_bound hn S a ha j
  apply deleted_row_bound_of_count_bounds S hS hSc a ha
  intro u hu
  have h := hbound u hu ε hε
  simpa only [hsplit, hn', Nat.add_assoc] using h

end Froberg.MonomialExpansion
