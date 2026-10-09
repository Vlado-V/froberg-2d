module

public import Froberg.PrefixGrowth
public import Froberg.PrefixPartialIncidence

@[expose] public section

/-! The strengthened subspace growth bound implies surjectivity at the first
possible generator count, via the sharp partial-row incidence charts. -/
noncomputable section
namespace Froberg.PrefixSurjectivity
open Module MvPolynomial Finset
open Quartic.PolynomialBilinearCoordinates
open PrefixPartialIncidence
variable {K : Type*} [Field K]

/-- A distinguished row and the remaining rows form an ordinary tuple. -/
def consEquiv (U : Type*) [AddCommGroup U] [Module K U] (q : ℕ) :
    ((Fin q → U) × U) ≃ₗ[K] (Fin (q + 1) → U) where
  toFun R := Fin.cons R.2 R.1
  invFun a := (Fin.tail a, a 0)
  left_inv R := by simp
  right_inv a := Fin.cons_self_tail a
  map_add' R S := by ext i; cases i using Fin.cases <;> simp
  map_smul' c R := by ext i; cases i using Fin.cases <;> simp

theorem span_cons {U : Type*} [AddCommGroup U] [Module K U] {q : ℕ}
    (R : (Fin q → U) × U) :
    Submodule.span K (Set.range (consEquiv (K := K) U q R)) =
      Submodule.span K (Set.range R.1) ⊔ K ∙ R.2 := by
  change Submodule.span K (Set.range (Fin.cons R.2 R.1)) = _
  rw [Fin.range_cons, Submodule.span_insert, sup_comm]

/-- Embed a partial final row by filling all unselected coordinates with zero. -/
def supportedEmbed {N q : ℕ} (T : Finset (Fin N)) :
    ((Fin q → Fin N → K) × (T → K)) →ₗ[K] Relations K N q where
  toFun R := (R.1, fun l => if h : l ∈ T then R.2 ⟨l, h⟩ else 0)
  map_add' R S := by
    apply Prod.ext
    · rfl
    · funext l
      by_cases h : l ∈ T <;> simp [h]
  map_smul' c R := by
    apply Prod.ext
    · rfl
    · funext l
      by_cases h : l ∈ T <;> simp [h]

theorem supportedEmbed_injective {N q : ℕ} (T : Finset (Fin N)) :
    Function.Injective (supportedEmbed (K := K) (q := q) T) := by
  intro R S h
  apply Prod.ext
  · exact congrArg (fun Z : Relations K N q => Z.1) h
  · funext l
    have hh := congrFun (congrArg Prod.snd h) l.val
    simpa [supportedEmbed, l.property] using hh

theorem supportedEmbed_support {N q : ℕ} (T : Finset (Fin N))
    (R : (Fin q → Fin N → K) × (T → K)) (l : Fin N) (hl : l ∉ T) :
    (supportedEmbed T R).2 l = 0 := by simp [supportedEmbed, hl]

variable {U V W : Type*}
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {q s : ℕ}

/-- Abstract surjectivity from uniform strengthened image growth. -/
theorem exists_surjective_of_growth [Infinite K]
    (B : (Fin (q + 1) → U) →ₗ[K] V →ₗ[K] W)
    (hN : 0 < finrank K U) (hs : s ≤ finrank K U)
    (hdim : finrank K W = q * finrank K U + s)
    (hgrowth : ∀ a : Fin (q + 1) → U,
      let k := finrank K (Submodule.span K (Set.range a))
      finrank K W * k + finrank K U * k * (finrank K U - k) ≤
        finrank K U * finrank K (B a).range) :
    ∃ v : V, Function.Surjective (B.flip v) := by
  classical
  let N := finrank K U
  let M := finrank K W
  let C := (tupleCoordinate B).comp (consEquiv (K := K) (Fin N → K) q).toLinearMap
  let T : Finset (Fin N) := univ.map (Fin.castLEEmb hs)
  have hT : T.card = s := by simp [T]
  have hC (R : Relations K N q) :
      finrank K (C R).range =
        finrank K (B (tupleDecode K U (q + 1) (consEquiv (K := K) (Fin N → K) q R))).range :=
    finrank_range_tupleCoordinate B _
  have hrank (R : Relations K N q) :
      finrank K (Submodule.span K (Set.range
        (tupleDecode K U (q + 1) (consEquiv (K := K) (Fin N → K) q R)))) =
      finrank K (rowSpan R) := by
    rw [finrank_span_tupleDecode, span_cons]
    rfl
  have hg (R : Relations K N q) :
      M * finrank K (rowSpan R) + N * finrank K (rowSpan R) * (N - finrank K (rowSpan R)) ≤
        N * finrank K (C R).range := by
    rw [hC]
    simpa only [hrank] using hgrowth
      (tupleDecode K U (q + 1) (consEquiv (K := K) (Fin N → K) q R))
  have hzero : ∀ F : Fin q → Fin N → K, F ≠ 0 →
      let r := finrank K (Submodule.span K (Set.range F))
      r * (N - r) + q * r ≤ finrank K (C (F, 0)).range := by
    intro F _
    dsimp only
    have h := hg (F, 0)
    have hspan : rowSpan (F, (0 : Fin N → K)) = Submodule.span K (Set.range F) := by
      change Submodule.span K (Set.range F) ⊔ K ∙ (0 : Fin N → K) = _
      rw [Submodule.span_zero_singleton, sup_bot_eq]
    rw [hspan] at h
    have hm : q * N ≤ M := by dsimp [M, N]; omega
    have hmk := Nat.mul_le_mul_right (finrank K (Submodule.span K (Set.range F))) hm
    nlinarith
  have hlast : ∀ R : Relations K N q, R.2 ≠ 0 →
      (∀ l, l ∉ T → R.2 l = 0) →
      let r := finrank K (rowSpan R)
      q * r + (r - 1) * (N - r) + T.card ≤ finrank K (C R).range := by
    intro R hnz _
    dsimp only
    let k := finrank K (rowSpan R)
    let H := M - finrank K (C R).range
    have hkN : k ≤ N := by simpa [k] using Submodule.finrank_le (rowSpan R)
    have hk : 0 < k := by
      by_contra h
      have hz : rowSpan R = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
      have hm : R.2 ∈ rowSpan R := (show K ∙ R.2 ≤ rowSpan R from le_sup_right) (Submodule.mem_span_singleton_self R.2)
      rw [hz] at hm
      exact hnz hm
    have hrM : finrank K (C R).range ≤ M := by
      simpa [M] using Submodule.finrank_le (C R).range
    have hHM : H + finrank K (C R).range = M := Nat.sub_add_cancel hrM
    have hkn : N - k + k = N := Nat.sub_add_cancel hkN
    have h := hg R
    have hnorm : N * (H + k * (N - k)) ≤ (N - k) * (q * N + s) := by
      change M = q * N + s at hdim
      have hHMN := congrArg (fun z : ℕ => N * z) hHM
      have hknM := congrArg (fun z : ℕ => z * M) hkn
      dsimp only [k] at hHMN hknM ⊢
      nlinarith
    have hb := PrefixPartialCharts.nonzero_last_row_rank_budget hN hs hk hkN hnorm
    rw [hT]
    change q * k + (k - 1) * (N - k) + s ≤ finrank K (C R).range
    change H + q * k + (k - 1) * (N - k) + s ≤ q * N + s at hb
    change M = q * N + s at hdim
    omega
  obtain ⟨x, hx⟩ := exists_injective_on_supported C T hzero hlast
  let L := (C.flip x).comp (supportedEmbed (K := K) (q := q) T)
  have hL : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro R hR
    have hz := hx (supportedEmbed T R) (supportedEmbed_support T R) hR
    exact supportedEmbed_injective T (by simpa using hz)
  have hdimL : finrank K ((Fin q → Fin N → K) × (T → K)) =
      finrank K (Fin (finrank K W) → K) := by
    simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_coe, smul_eq_mul, mul_one]
    rw [hT]
    exact hdim.symm
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimL).mp hL
  refine ⟨(coordinates K V).symm x, ?_⟩
  intro w
  obtain ⟨R, hR⟩ := hsurj (coordinates K W w)
  refine ⟨tupleDecode K U (q + 1) (consEquiv (K := K) (Fin N → K) q (supportedEmbed T R)), ?_⟩
  apply (coordinates K W).injective
  exact hR

end Froberg.PrefixSurjectivity

namespace Froberg
open Module
variable {K : Type*} [Field K] [Infinite K] {n d e q s r : ℕ}

/-- Surjectivity at a partial-row count `M=q*N+s`. -/
theorem exists_prefix_surjective_at_partial_count (hn : 0 < n) (hed : e < d)
    (hlarge : (e + d).choose e * ((e + d).choose e * d.choose e) ≤ n)
    (hs : s ≤ (n + e - 1).choose e)
    (hdim : (n + (d + e) - 1).choose (d + e) = q * (n + e - 1).choose e + s) :
    ∃ f : Fin (q + 1) → Forms K n d, Function.Surjective (prefixMultiplication f e) := by
  have hN : 0 < finrank K (Forms K n e) := by
    rw [finrank_forms K n e hn]
    exact monomial_count_pos hn e
  have hS : s ≤ finrank K (Forms K n e) := by rwa [finrank_forms K n e hn]
  have hM : finrank K (Forms K n (d + e)) = q * finrank K (Forms K n e) + s := by
    simpa only [finrank_forms K n (d + e) hn, finrank_forms K n e hn] using hdim
  obtain ⟨f, hf⟩ := PrefixSurjectivity.exists_surjective_of_growth
    (prefixBilinear (K := K) (n := n) (d := d) (e := e) (r := q + 1)) hN hS hM (by
      intro a
      dsimp only
      have hg := homogeneous_subspace_growth hn hed hlarge (familySpace a) (familySpace_homogeneous a)
      rw [finrank_familySpace] at hg
      have h₁ := prefix_incidence_rank_add_hilbert (d := d) hn a
      have h₂ := prefix_hilbert_add_product_rank (d := d) hn a
      rw [Nat.add_comm e d] at h₂ hg
      have hrank : finrank K (prefixBilinear (d := d) a).range =
          finrank K (familySpace a * Forms K n d) := by
        change finrank K (prefixIncidenceFiber (d := d) a).range = _
        omega
      simpa only [finrank_forms K n (d + e) hn, finrank_forms K n e hn, hrank] using hg)
  refine ⟨f, ?_⟩
  rwa [prefixBilinear_flip] at hf

/-- Extra zero generators preserve surjectivity of homogeneous multiplication. -/
theorem exists_prefix_surjective_mono {r t : ℕ} (hrt : r ≤ t)
    (h : ∃ f : Fin r → Forms K n d, Function.Surjective (prefixMultiplication f e)) :
    ∃ f : Fin t → Forms K n d, Function.Surjective (prefixMultiplication f e) := by
  induction t, hrt using Nat.le_induction with
  | base => exact h
  | succ t hrt ih =>
      obtain ⟨f, hf⟩ := ih
      refine ⟨Fin.cons 0 f, ?_⟩
      intro y
      obtain ⟨a, ha⟩ := hf y
      refine ⟨Fin.cons 0 a, ?_⟩
      apply Subtype.ext
      simpa [prefixMultiplication_val, Fin.sum_univ_succ] using congrArg Subtype.val ha

/-- Every generator count on the surjective side has an actual witness. -/
theorem exists_prefix_surjective_of_large_variables (hn : 0 < n) (hed : e < d)
    (hlarge : (e + d).choose e * ((e + d).choose e * d.choose e) ≤ n)
    (hr : (n + (d + e) - 1).choose (d + e) ≤ r * (n + e - 1).choose e) :
    ∃ f : Fin r → Forms K n d, Function.Surjective (prefixMultiplication f e) := by
  let N := (n + e - 1).choose e
  let M := (n + (d + e) - 1).choose (d + e)
  have hN : 0 < N := monomial_count_pos hn e
  by_cases heq : M = r * N
  · obtain ⟨f, hf⟩ := exists_prefix_injective_of_large_variables (K := K) (r := r) hn hed hlarge (by change r * N ≤ M; omega)
    refine ⟨f, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hf⟩
    simp only [Module.finrank_pi_fintype, finrank_forms K n (d + e) hn,
      finrank_forms K n e hn, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact heq.symm
  · have hcount : M / N + 1 ≤ r := by
      have hlt : M < r * N := lt_of_le_of_ne hr heq
      exact Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul hN).mpr hlt)
    apply exists_prefix_surjective_mono hcount
    exact exists_prefix_surjective_at_partial_count (q := M / N) (s := M % N) hn hed hlarge
      (Nat.le_of_lt (Nat.mod_lt M hN)) (by
        change M = M / N * N + M % N
        simpa only [Nat.mul_comm] using (Nat.div_add_mod M N).symm)

end Froberg
