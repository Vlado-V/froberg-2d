module

public import Froberg.BalancedProfilePolynomial
public import Froberg.BinomialParityMargin
public import Froberg.SplitWeights

@[expose] public section

/-! Uniform scalar row retention after removing one parity and one further
bidegree. The estimate is the quarter-mass estimate in B.4. -/
noncomputable section
namespace Froberg
open Finset Filter
open scoped Topology

def retainedProfileIncrements (d i p j : ℕ) : Finset ℕ :=
  (parityBinomialIndices d i p).filter (fun u => i+u ≠ j)

theorem retainedProfileIncrements_mem {d i p j u : ℕ} :
    u ∈ retainedProfileIncrements d i p j ↔
      u ≤ d ∧ (i+u)%2 ≠ p ∧ i+u ≠ j := by
  simp only [retainedProfileIncrements, parityBinomialIndices, mem_filter, mem_range]
  omega

theorem eventually_balanced_profile_count_bounds {d : ℕ} (hd : 9 ≤ d) (e : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ i ≤ e, ∀ p < 2, ∀ j : ℕ, ∀ ε ≤ 1,
      (2*m+ε+e+d-1).choose d ≤
        4 * ∑ u ∈ retainedProfileIncrements d i p j,
          (m+i+u-1).choose u * (m+ε+(e-i)+(d-u)-1).choose (d-u) := by
  have h : ∀ᶠ m : ℕ in atTop, ∀ i : Fin (e+1), ∀ p : Fin 2,
      ∀ j : Fin (e+d+2), ∀ ε : Fin 2,
      (2*m+ε.val+e+d-1).choose d ≤
        4 * ∑ u ∈ retainedProfileIncrements d i.val p.val j.val,
          (m+i.val+u-1).choose u *
            (m+ε.val+(e-i.val)+(d-u)-1).choose (d-u) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro p
    apply eventually_all.mpr
    intro j
    apply eventually_all.mpr
    intro ε
    have hmass := parity_binomial_mass_except_margin hd i.val p.val j.val p.isLt
    have hpos : 0 < 2^d := by positivity
    have hgap : 2^d < 4 * ∑ u ∈ retainedProfileIncrements d i.val p.val j.val,
        d.choose u := by
      change 2^d < 4 * ∑ u ∈ (parityBinomialIndices d i.val p.val).filter
        (fun u => i.val+u ≠ j.val), d.choose u
      omega
    have hb := eventually_balanced_profile_sum_bound d
      (retainedProfileIncrements d i.val p.val j.val)
      (fun u hu => (retainedProfileIncrements_mem.mp hu).1) hgap
      i.val (ε.val+(e-i.val)) (ε.val+e)
    simpa only [Nat.add_assoc] using hb
  filter_upwards [h] with m hm
  intro i hi p hp j ε hε
  let j' := min j (e+d+1)
  have hU : retainedProfileIncrements d i p j = retainedProfileIncrements d i p j' := by
    ext u
    rw [retainedProfileIncrements_mem,retainedProfileIncrements_mem]
    dsimp only [j']
    omega
  rw [hU]
  exact hm ⟨i,by omega⟩ ⟨p,hp⟩ ⟨j',by dsimp [j']; omega⟩ ⟨ε,by omega⟩

namespace MonomialExpansion

/-- A disjoint union of retained bidegrees gives a lower bound for the
actual weighted monomial row. -/
theorem profile_row_bound_of_count_bound {n d e : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (a : Fin n →₀ ℕ) (ha : a.degree=e) (p j : ℕ)
    (hcount : (n+e+d-1).choose d ≤
      4 * ∑ u ∈ retainedProfileIncrements d (partialDegree S a) p j,
        (S.card+partialDegree S a+u-1).choose u *
          (Sᶜ.card+(e-partialDegree S a)+(d-u)-1).choose (d-u)) :
    (n+e+d-1).choose d ≤
      4 * ∑ b ∈ (exponents n (e+d)).filter
        (fun b => partialDegree S b % 2 ≠ p ∧ partialDegree S b ≠ j), weight b a := by
  let U := retainedProfileIncrements d (partialDegree S a) p j
  let F (u : ℕ) := (exponents n (e+d)).filter
    (fun b => partialDegree S b = partialDegree S a+u)
  have hc : partialDegree Sᶜ a = e-partialDegree S a := by
    have h := partialDegree_add_compl S a
    omega
  have hformula (u : ℕ) (hu : u ∈ U) :
      ∑ b ∈ F u, weight b a =
        (S.card+partialDegree S a+u-1).choose u *
          (Sᶜ.card+(e-partialDegree S a)+(d-u)-1).choose (d-u) := by
    have hud := (retainedProfileIncrements_mem.mp hu).1
    have h := sum_weight_target_bidegree S hS hSc a u (d-u)
    rw [Nat.add_sub_of_le hud,ha,hc] at h
    exact h
  have hdis : Set.PairwiseDisjoint (↑U) F := by
    intro u hu v hv huv
    apply disjoint_left.mpr
    intro b hb hc
    have h₁ := (mem_filter.mp hb).2
    have h₂ := (mem_filter.mp hc).2
    exact huv (by omega)
  have hsub : U.biUnion F ⊆ (exponents n (e+d)).filter
      (fun b => partialDegree S b % 2 ≠ p ∧ partialDegree S b ≠ j) := by
    intro b hb
    obtain ⟨u,hu,hb⟩ := mem_biUnion.mp hb
    obtain ⟨hbu,hbe⟩ := mem_filter.mp hb
    obtain ⟨hud,hup,huj⟩ := retainedProfileIncrements_mem.mp hu
    exact mem_filter.mpr ⟨hbu,by simpa only [hbe] using And.intro hup huj⟩
  have hs : (∑ u ∈ U,
      (S.card+partialDegree S a+u-1).choose u *
        (Sᶜ.card+(e-partialDegree S a)+(d-u)-1).choose (d-u)) ≤
      ∑ b ∈ (exponents n (e+d)).filter
        (fun b => partialDegree S b % 2 ≠ p ∧ partialDegree S b ≠ j), weight b a := by
    calc
      _ = ∑ u ∈ U, ∑ b ∈ F u, weight b a := sum_congr rfl (fun u hu => (hformula u hu).symm)
      _ = ∑ b ∈ U.biUnion F, weight b a := (sum_biUnion hdis).symm
      _ ≤ _ := sum_le_sum_of_subset hsub
  exact hcount.trans (Nat.mul_le_mul_left 4 hs)

/-- One threshold works for every source monomial, every deleted parity,
and every additional excluded bidegree. -/
theorem exists_parity_profile_row_threshold {d : ℕ} (hd : 9 ≤ d) (e : ℕ) :
    ∃ m₀ : ℕ, ∀ (n : ℕ) (S : Finset (Fin n)),
      m₀ ≤ S.card → S.card ≤ Sᶜ.card → Sᶜ.card ≤ S.card+1 →
      ∀ a : Fin n →₀ ℕ, a.degree=e → ∀ p < 2, ∀ j : ℕ,
        (n+e+d-1).choose d ≤
          4 * ∑ b ∈ (exponents n (e+d)).filter
            (fun b => partialDegree S b % 2 ≠ p ∧ partialDegree S b ≠ j), weight b a := by
  obtain ⟨m₁,hm₁⟩ := eventually_atTop.mp (eventually_balanced_profile_count_bounds hd e)
  refine ⟨max 1 m₁,?_⟩
  intro n S hm hle hupper a ha p hp j
  have hpos : 0<S.card := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hm)
  have hS : S.Nonempty := card_pos.mp hpos
  have hSc : Sᶜ.Nonempty := card_pos.mp (hpos.trans_le hle)
  let ε := Sᶜ.card-S.card
  have hε : ε≤1 := by dsimp [ε]; omega
  have hsplit : Sᶜ.card = S.card+ε := by dsimp [ε]; omega
  have hcard : S.card+Sᶜ.card=n := by simpa using card_add_card_compl S
  have hn' : n=2*S.card+ε := by omega
  have hi : partialDegree S a≤e := ha ▸ partialDegree_le_degree S a
  apply profile_row_bound_of_count_bound S hS hSc a ha p j
  have h := hm₁ S.card ((le_max_right _ _).trans hm) (partialDegree S a) hi p hp j ε hε
  simpa only [hsplit,hn',Nat.add_assoc] using h

end MonomialExpansion
end Froberg
