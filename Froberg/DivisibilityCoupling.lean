import Froberg.MonomialIncidence
import Mathlib

/-! The uniform divisibility coupling, with exact source and target
marginals for all monomials, including repeated variables. -/
noncomputable section
namespace Froberg.MonomialExpansion
open Finset

lemma source_weight_sum {n d : ℕ} (b : Degree n d) (e : ℕ) :
    ∑ a : Degree n e, weight b.val a.val = d.choose e := by
  simpa only [Degree, sum_coe_sort, degree_val] using sum_weight_sources b.val e

lemma target_weight_sum {n e d : ℕ} (hn : 0 < n) (hed : e ≤ d) (a : Degree n e) :
    ∑ b : Degree n d, weight b.val a.val = (n + d - 1).choose (d - e) := by
  have h := sum_weight_targets hn a.val (d - e)
  rw [degree_val, show e + (d - e) = d by omega,
    show n + e + (d - e) - 1 = n + d - 1 by omega] at h
  rw [sum_coe_sort (exponents n d) (fun b => weight b a.val)]
  exact h

lemma monomial_weight_balance {n e d : ℕ} (hn : 0 < n) (hed : e ≤ d) :
    (n + e - 1).choose e * (n + d - 1).choose (d - e) =
      (n + d - 1).choose d * d.choose e := by
  have h : (∑ a : Degree n e, ∑ b : Degree n d, weight b.val a.val) =
      ∑ b : Degree n d, ∑ a : Degree n e, weight b.val a.val := sum_comm
  simpa only [target_weight_sum hn hed, source_weight_sum, sum_const, card_univ,
    card_degree, smul_eq_mul] using h

/-- Joint probability for a uniform source monomial and a uniform target
monomial, supported exactly on divisibility. -/
def divisibilityCoupling {n e d : ℕ} (a : Degree n e) (b : Degree n d) : ℝ :=
  (weight b.val a.val : ℝ) / ((n + d - 1).choose d * d.choose e : ℝ)

lemma divisibilityCoupling_column {n e d : ℕ} (hn : 0 < n) (hed : e ≤ d)
    (b : Degree n d) :
    ∑ a : Degree n e, divisibilityCoupling a b = 1 / ((n + d - 1).choose d : ℝ) := by
  have hc : (d.choose e : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hed).ne'
  have hn' : ((n + d - 1).choose d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show d ≤ n + d - 1 by omega)).ne'
  unfold divisibilityCoupling
  rw [← sum_div, ← Nat.cast_sum, source_weight_sum]
  field_simp

lemma divisibilityCoupling_row {n e d : ℕ} (hn : 0 < n) (hed : e ≤ d)
    (a : Degree n e) :
    ∑ b : Degree n d, divisibilityCoupling a b = 1 / ((n + e - 1).choose e : ℝ) := by
  have he' : ((n + e - 1).choose e : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show e ≤ n + e - 1 by omega)).ne'
  have hd' : ((n + d - 1).choose d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show d ≤ n + d - 1 by omega)).ne'
  have hc : (d.choose e : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hed).ne'
  have hb : ((n + e - 1).choose e : ℝ) * (n + d - 1).choose (d - e) =
      ((n + d - 1).choose d : ℝ) * d.choose e := by
    exact_mod_cast monomial_weight_balance hn hed
  unfold divisibilityCoupling
  rw [← sum_div, ← Nat.cast_sum, target_weight_sum hn hed]
  field_simp
  nlinarith

lemma divisibilityCoupling_nonneg {n e d : ℕ} (a : Degree n e) (b : Degree n d) :
    0 ≤ divisibilityCoupling a b := by unfold divisibilityCoupling; positivity

lemma divisibilityCoupling_pos_iff {n e d : ℕ} (hn : 0 < n) (hed : e ≤ d)
    (a : Degree n e) (b : Degree n d) : 0 < divisibilityCoupling a b ↔ a.val ≤ b.val := by
  have hden : (0 : ℝ) < ((n + d - 1).choose d : ℝ) * d.choose e := by
    have h₁ : (0 : ℝ) < (n + d - 1).choose d := by
      exact_mod_cast Nat.choose_pos (show d ≤ n + d - 1 by omega)
    have h₂ : (0 : ℝ) < d.choose e := by exact_mod_cast Nat.choose_pos hed
    positivity
  rw [divisibilityCoupling, div_pos_iff_of_pos_right hden, Nat.cast_pos, weight_pos_iff]

lemma divisibilityCoupling_lower {n e d : ℕ} (hn : 0 < n) (hed : e ≤ d)
    (a : Degree n e) (b : Degree n d) (hab : a.val ≤ b.val) :
    1 / (((n + d - 1).choose d : ℝ) * d.choose e) ≤ divisibilityCoupling a b := by
  have hw : (1 : ℝ) ≤ weight b.val a.val := by
    exact_mod_cast (weight_pos_iff b.val a.val).mpr hab
  exact div_le_div_of_nonneg_right hw (by positivity)

end Froberg.MonomialExpansion
