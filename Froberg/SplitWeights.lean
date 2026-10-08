import Froberg.MonomialIncidence

/-! Exact weighted row sums after separating the variables into two blocks. -/
noncomputable section
namespace Froberg.MonomialExpansion
open Finset PowerSeries

def partialDegree {n : ℕ} (S : Finset (Fin n)) (a : Fin n →₀ ℕ) : ℕ := ∑ i ∈ S, a i

theorem partialDegree_add {n : ℕ} (S : Finset (Fin n)) (a b : Fin n →₀ ℕ) :
    partialDegree S (a + b) = partialDegree S a + partialDegree S b := by
  simp [partialDegree, sum_add_distrib]

theorem partialDegree_add_compl {n : ℕ} (S : Finset (Fin n)) (a : Fin n →₀ ℕ) :
    partialDegree S a + partialDegree Sᶜ a = a.degree := by
  rw [partialDegree, partialDegree, sum_add_sum_compl, Finsupp.degree_eq_sum]

theorem partialDegree_le_degree {n : ℕ} (S : Finset (Fin n)) (a : Fin n →₀ ℕ) :
    partialDegree S a ≤ a.degree := by
  have h := partialDegree_add_compl S a
  omega

theorem degree_filter {n : ℕ} (S : Finset (Fin n)) (a : Fin n →₀ ℕ) :
    (a.filter (· ∈ S)).degree = partialDegree S a := by
  rw [Finsupp.degree_eq_sum]
  simp [partialDegree, Finsupp.filter_apply, sum_ite_mem]

theorem filter_mem_antidiag {n : ℕ} (S : Finset (Fin n)) (a : Fin n →₀ ℕ) :
    a.filter (· ∈ S) ∈ finsuppAntidiag S (partialDegree S a) := by
  rw [mem_finsuppAntidiag']
  refine ⟨degree_filter S a, ?_⟩
  intro i hi
  exact (mem_filter.mp hi).2

theorem extension_weight_on_support {n : ℕ} (S : Finset (Fin n))
    (a c : Fin n →₀ ℕ) (hc : c.support ⊆ S) :
    weight (a + c) a = ∏ i ∈ S, (a i + c i).choose (a i) := by
  unfold weight
  symm
  apply prod_subset (subset_univ S)
  intro i _ hi
  have hc0 : c i = 0 := Finsupp.notMem_support_iff.mp (fun h => hi (hc h))
  simp [hc0]

/-- Total extension weight in one nonempty block of variables. -/
theorem sum_weight_extensions_block {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (a : Fin n →₀ ℕ) (d : ℕ) :
    ∑ c ∈ finsuppAntidiag S d, weight (a + c) a =
      (S.card + partialDegree S a + d - 1).choose d := by
  let g : PowerSeries ℤ := mk 1
  let f : Fin n → PowerSeries ℤ := fun i => g ^ (a i + 1)
  have hc (i : Fin n) (j : ℕ) : coeff j (f i) = ((a i + j).choose (a i) : ℤ) := by
    change PowerSeries.coeff j ((mk 1 : PowerSeries ℤ) ^ (a i + 1)) = _
    rw [mk_one_pow_eq_mk_choose_add, coeff_mk]
  have hs : ∑ i ∈ S, (a i + 1) = partialDegree S a + S.card := by
    simp [partialDegree, sum_add_distrib]
  have hp : ∏ i ∈ S, f i = g ^ (partialDegree S a + S.card) := by
    simp only [f]
    rw [prod_pow_eq_pow_sum, hs]
  have hpos := card_pos.mpr hS
  have h := PowerSeries.coeff_prod f d S
  rw [hp, show partialDegree S a + S.card = (partialDegree S a + S.card - 1) + 1 by omega,
    show g = (mk 1 : PowerSeries ℤ) from rfl, mk_one_pow_eq_mk_choose_add, coeff_mk] at h
  simp only [hc] at h
  have hh : (∑ c ∈ finsuppAntidiag S d, ∏ i ∈ S, (a i + c i).choose (a i) : ℕ) =
      (partialDegree S a + S.card - 1 + d).choose (partialDegree S a + S.card - 1) := by
    exact_mod_cast h.symm
  have he : ∑ c ∈ finsuppAntidiag S d, weight (a + c) a =
      ∑ c ∈ finsuppAntidiag S d, ∏ i ∈ S, (a i + c i).choose (a i) := by
    apply sum_congr rfl
    intro c hc
    exact extension_weight_on_support S a c (mem_finsuppAntidiag'.mp hc).2
  rw [he, hh, show S.card + partialDegree S a + d - 1 =
    partialDegree S a + S.card - 1 + d by omega]
  exact Nat.choose_symm_of_eq_add rfl

theorem extension_weight_split {n : ℕ} (S : Finset (Fin n)) (a c₁ c₂ : Fin n →₀ ℕ)
    (h₁ : c₁.support ⊆ S) (h₂ : c₂.support ⊆ Sᶜ) :
    weight (a + (c₁ + c₂)) a = weight (a + c₁) a * weight (a + c₂) a := by
  rw [extension_weight_on_support S a c₁ h₁, extension_weight_on_support Sᶜ a c₂ h₂]
  unfold weight
  rw [← prod_mul_prod_compl S]
  congr 1
  · apply prod_congr rfl
    intro i hi
    have hc : c₂ i = 0 := Finsupp.notMem_support_iff.mp (fun h => (mem_compl.mp (h₂ h)) hi)
    simp [hc]
  · apply prod_congr rfl
    intro i hi
    have hc : c₁ i = 0 := Finsupp.notMem_support_iff.mp (fun h => (mem_compl.mp hi) (h₁ h))
    simp [hc]

/-- The exact row weight of a fixed extension bidegree. -/
theorem sum_weight_split_extensions {n : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) (a : Fin n →₀ ℕ) (u v : ℕ) :
    ∑ p ∈ (finsuppAntidiag S u).product (finsuppAntidiag Sᶜ v),
        weight (a + (p.1 + p.2)) a =
      (S.card + partialDegree S a + u - 1).choose u *
        (Sᶜ.card + partialDegree Sᶜ a + v - 1).choose v := by
  calc
    _ = ∑ p ∈ (finsuppAntidiag S u).product (finsuppAntidiag Sᶜ v),
        weight (a + p.1) a * weight (a + p.2) a := by
      apply sum_congr rfl
      intro p hp
      exact extension_weight_split S a p.1 p.2
        (mem_finsuppAntidiag'.mp (mem_product.mp hp).1).2
        (mem_finsuppAntidiag'.mp (mem_product.mp hp).2).2
    _ = _ := by
      simp only [Finset.product_eq_sprod]
      rw [Finset.sum_product (finsuppAntidiag S u) (finsuppAntidiag Sᶜ v)
        (fun p => weight (a + p.1) a * weight (a + p.2) a)]
      dsimp only
      rw [← sum_mul_sum, sum_weight_extensions_block S hS,
        sum_weight_extensions_block Sᶜ hSc]

theorem filter_add_of_block_support {n : ℕ} (S : Finset (Fin n))
    (c₁ c₂ : Fin n →₀ ℕ) (h₁ : c₁.support ⊆ S) (h₂ : c₂.support ⊆ Sᶜ) :
    (c₁ + c₂).filter (· ∈ S) = c₁ := by
  ext i
  by_cases hi : i ∈ S
  · have hc : c₂ i = 0 := Finsupp.notMem_support_iff.mp (fun h => (mem_compl.mp (h₂ h)) hi)
    simp [Finsupp.filter_apply, hi, hc]
  · have hc : c₁ i = 0 := Finsupp.notMem_support_iff.mp (fun h => hi (h₁ h))
    simp [Finsupp.filter_apply, hi, hc]

theorem filter_add_compl {n : ℕ} (S : Finset (Fin n)) (c : Fin n →₀ ℕ) :
    c.filter (· ∈ S) + c.filter (· ∈ Sᶜ) = c := by
  simpa only [mem_compl] using Finsupp.filter_add_filter_not c (· ∈ S)

/-- The block formula applies to an ordinary degree slice selected by its
degree in the first block. -/
theorem sum_weight_filtered_extensions {n : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) (a : Fin n →₀ ℕ) (u v : ℕ) :
    ∑ c ∈ (exponents n (u + v)).filter (fun c => partialDegree S c = u),
        weight (a + c) a =
      (S.card + partialDegree S a + u - 1).choose u *
        (Sᶜ.card + partialDegree Sᶜ a + v - 1).choose v := by
  rw [← sum_weight_split_extensions S hS hSc a u v]
  apply sum_bij (fun c _ => (c.filter (· ∈ S), c.filter (· ∈ Sᶜ)))
  · intro c hc
    obtain ⟨hcdeg, hcu⟩ := mem_filter.mp hc
    have hcv : partialDegree Sᶜ c = v := by
      have h := partialDegree_add_compl S c
      rw [mem_exponents.mp hcdeg, hcu] at h
      omega
    exact mem_product.mpr ⟨hcu ▸ filter_mem_antidiag S c, hcv ▸ filter_mem_antidiag Sᶜ c⟩
  · intro c hc b hb hcb
    have h₁ := congrArg Prod.fst hcb
    have h₂ := congrArg Prod.snd hcb
    dsimp only at h₁ h₂
    calc
      c = c.filter (· ∈ S) + c.filter (· ∈ Sᶜ) := (filter_add_compl S c).symm
      _ = b.filter (· ∈ S) + b.filter (· ∈ Sᶜ) := by rw [h₁, h₂]
      _ = b := filter_add_compl S b
  · intro p hp
    obtain ⟨h₁, h₂⟩ := mem_product.mp hp
    have hc₁ := (mem_finsuppAntidiag'.mp h₁).2
    have hc₂ := (mem_finsuppAntidiag'.mp h₂).2
    have hd₁ : p.1.degree = u := (mem_finsuppAntidiag'.mp h₁).1
    have hd₂ : p.2.degree = v := (mem_finsuppAntidiag'.mp h₂).1
    have hf₁ := filter_add_of_block_support S p.1 p.2 hc₁ hc₂
    have hf₂ : (p.1 + p.2).filter (· ∈ Sᶜ) = p.2 := by
      simpa only [compl_compl, add_comm] using filter_add_of_block_support Sᶜ p.2 p.1 hc₂ (by simpa using hc₁)
    refine ⟨p.1 + p.2, mem_filter.mpr ⟨mem_exponents.mpr (by simp [hd₁, hd₂]), ?_⟩, ?_⟩
    · rw [← degree_filter S, hf₁, hd₁]
    · exact Prod.ext hf₁ hf₂
  · intro c hc
    rw [filter_add_compl]

/-- Exact row weight in a target bidegree, expressed using the two block sizes. -/
theorem sum_weight_target_bidegree {n : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) (a : Fin n →₀ ℕ) (u v : ℕ) :
    ∑ b ∈ (exponents n (a.degree + (u + v))).filter
        (fun b => partialDegree S b = partialDegree S a + u), weight b a =
      (S.card + partialDegree S a + u - 1).choose u *
        (Sᶜ.card + partialDegree Sᶜ a + v - 1).choose v := by
  rw [← sum_weight_filtered_extensions S hS hSc a u v]
  apply sum_bij_ne_zero (fun b _ _ => b - a)
  · intro b hb hw
    obtain ⟨hbdeg, hbu⟩ := mem_filter.mp hb
    have hab := (weight_ne_zero_iff b a).mp hw
    have he : a + (b - a) = b := add_tsub_cancel_of_le hab
    have hd := congrArg Finsupp.degree he
    have hp := congrArg (partialDegree S) he
    rw [map_add, mem_exponents.mp hbdeg] at hd
    rw [partialDegree_add, hbu] at hp
    exact mem_filter.mpr ⟨mem_exponents.mpr (by omega), by omega⟩
  · intro b hb hw c hc hv heq
    have hab := (weight_ne_zero_iff b a).mp hw
    have hac := (weight_ne_zero_iff c a).mp hv
    calc
      b = a + (b - a) := (add_tsub_cancel_of_le hab).symm
      _ = a + (c - a) := by rw [heq]
      _ = c := add_tsub_cancel_of_le hac
  · intro c hc hw
    obtain ⟨hcdeg, hcu⟩ := mem_filter.mp hc
    refine ⟨a + c, mem_filter.mpr ⟨mem_exponents.mpr ?_, ?_⟩, ?_, ?_⟩
    · rw [map_add, mem_exponents.mp hcdeg]
    · rw [partialDegree_add, hcu]
    · exact (weight_ne_zero_iff _ _).mpr (le_add_right le_rfl)
    · exact add_tsub_cancel_left a c
  · intro b hb hw
    rw [add_tsub_cancel_of_le ((weight_ne_zero_iff b a).mp hw)]

theorem target_bidegree_possible {n d : ℕ} (S : Finset (Fin n))
    (a b : Fin n →₀ ℕ) (hb : b.degree = a.degree + d) (hw : weight b a ≠ 0) :
    ∃ u ≤ d, partialDegree S b = partialDegree S a + u := by
  have hab := (weight_ne_zero_iff b a).mp hw
  have he : a + (b - a) = b := add_tsub_cancel_of_le hab
  have hd := congrArg Finsupp.degree he
  rw [map_add, hb] at hd
  have hp := congrArg (partialDegree S) he
  rw [partialDegree_add] at hp
  refine ⟨partialDegree S (b - a), ?_, hp.symm⟩
  have h := partialDegree_le_degree S (b - a)
  omega

end Froberg.MonomialExpansion
