import Froberg.DivertedTransport

/-! Finite binomial weights and their polynomial generating functions.
These supply exact, rather than asymptotic, profile identities. -/
noncomputable section
namespace Froberg
open Polynomial Finset

def profileBinomial (σ : ℝ) (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * σ ^ k * (1 - σ) ^ (n - k)

def profilePolynomial (σ : ℝ) (n : ℕ) : Polynomial ℝ :=
  (C σ * X + C (1 - σ)) ^ n

theorem profilePolynomial_coeff (σ : ℝ) (n k : ℕ) :
    (profilePolynomial σ n).coeff k = profileBinomial σ n k := by
  have hid : profilePolynomial σ n = ((X + C (1 - σ)) ^ n).comp (C σ * X) := by
    simp only [pow_comp, add_comp, X_comp, C_comp, profilePolynomial]
  rw [hid, comp_C_mul_X_coeff, coeff_X_add_C_pow]
  unfold profileBinomial
  ring

theorem profilePolynomial_degree (σ : ℝ) (n : ℕ) :
    (profilePolynomial σ n).natDegree ≤ n := by
  have h : (C σ * X + C (1 - σ)).natDegree ≤ 1 := by compute_degree
  rw [profilePolynomial, natDegree_pow]
  simpa using Nat.mul_le_mul_left n h

@[simp] theorem profilePolynomial_eval_one (σ : ℝ) (n : ℕ) :
    (profilePolynomial σ n).eval 1 = 1 := by
  simp [profilePolynomial]

theorem profileBinomial_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (n k : ℕ) :
    0 ≤ profileBinomial σ n k := by
  unfold profileBinomial
  positivity

theorem profileBinomial_pos {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    {n k : ℕ} (hk : k ≤ n) : 0 < profileBinomial σ n k := by
  have hc : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  unfold profileBinomial
  positivity

@[simp] theorem profileBinomial_top (σ : ℝ) (n : ℕ) :
    profileBinomial σ n n = σ ^ n := by simp [profileBinomial]

theorem profileBinomial_above (σ : ℝ) {n k : ℕ} (hk : n < k) :
    profileBinomial σ n k = 0 := by simp [profileBinomial, Nat.choose_eq_zero_of_lt hk]

theorem profileBinomial_sum (σ : ℝ) (n : ℕ) :
    ∑ k : Fin (n + 1), profileBinomial σ n k = 1 := by
  have hh := (profilePolynomial σ n).eval_eq_sum_range'
    (by have := profilePolynomial_degree σ n; omega : (profilePolynomial σ n).natDegree < n + 1) 1
  simpa only [profilePolynomial_eval_one, profilePolynomial_coeff, one_pow, mul_one,
    Fin.sum_univ_eq_sum_range] using hh.symm

theorem profilePolynomial_truncated (σ : ℝ) (s : ℕ) :
    ∑ i : Fin s, monomial (i : ℕ) (profileBinomial σ s i) =
      profilePolynomial σ s - monomial s (σ ^ s) := by
  have hh := (profilePolynomial σ s).as_sum_range' (s + 1)
    (by have := profilePolynomial_degree σ s; omega)
  simp only [sum_range_succ, profilePolynomial_coeff, profileBinomial_top] at hh
  rw [Fin.sum_univ_eq_sum_range (fun k => (monomial k (profileBinomial σ s k) : Polynomial ℝ)) s]
  exact eq_sub_of_add_eq hh.symm

theorem profileBinomial_partial_sum (σ : ℝ) (s : ℕ) :
    ∑ i : Fin s, profileBinomial σ s i = 1 - σ ^ s := by
  have hh := congrArg (fun P : Polynomial ℝ => P.eval 1) (profilePolynomial_truncated σ s)
  simpa only [eval_finset_sum, eval_monomial, one_pow, mul_one, eval_sub,
    profilePolynomial_eval_one] using hh

def profileConditional (σ : ℝ) (s : ℕ) (i : Fin s) : ℝ :=
  profileBinomial σ s i / (1 - σ ^ s)

theorem profileConditional_pos {σ : ℝ} {s : ℕ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s) (i : Fin s) :
    0 < profileConditional σ s i := by
  have hp : σ ^ s < 1 := pow_lt_one₀ hσ.le hσ1 (by omega)
  exact div_pos (profileBinomial_pos hσ hσ1 (by omega)) (sub_pos.mpr hp)

theorem profileConditional_sum {σ : ℝ} {s : ℕ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s) :
    ∑ i : Fin s, profileConditional σ s i = 1 := by
  have hp : σ ^ s < 1 := pow_lt_one₀ hσ.le hσ1 (by omega)
  simp only [profileConditional, ← sum_div, profileBinomial_partial_sum]
  exact div_self (by linarith)

def profileShift {s : ℕ} (i : Fin s) (z : Fin (s + 2)) : Fin (2 * s + 1) :=
  ⟨i + z, by omega⟩

theorem profileShift_injective {s : ℕ} (i : Fin s) :
    Function.Injective (profileShift i) := by
  intro z z' h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp only [profileShift] at this
  omega

def profileJoint (σ : ℝ) (s : ℕ) (i : Fin s) (j : Fin (2 * s + 1)) : ℝ :=
  profileConditional σ s i * ∑ z : Fin (s + 2),
    if profileShift i z = j then profileBinomial σ (s + 1) z else 0

def profileMark (σ : ℝ) (s : ℕ) (z : Fin (s + 2)) : ℝ :=
  if (z : ℕ) = s then σ ^ s * (1 - σ) else
  if (z : ℕ) = s + 1 then σ ^ (s + 1) else 0

def profileMarkedJoint (σ : ℝ) (s : ℕ) (i : Fin s) (j : Fin (2 * s + 1)) : ℝ :=
  profileConditional σ s i * ∑ z : Fin (s + 2),
    if profileShift i z = j then profileMark σ s z else 0

theorem profileJoint_row (σ : ℝ) (s : ℕ) (i : Fin s) :
    ∑ j, profileJoint σ s i j = profileConditional σ s i := by
  simp only [profileJoint, ← mul_sum]
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, if_true]
  rw [show s + 2 = (s + 1) + 1 by omega, profileBinomial_sum, mul_one]

theorem profileMark_sum (σ : ℝ) (s : ℕ) :
    ∑ z : Fin (s + 2), profileMark σ s z = σ ^ s := by
  have hid (z : Fin (s + 2)) : profileMark σ s z =
      (if z = (⟨s, by omega⟩ : Fin (s + 2)) then σ ^ s * (1 - σ) else 0) +
      (if z = (⟨s + 1, by omega⟩ : Fin (s + 2)) then σ ^ (s + 1) else 0) := by
    unfold profileMark
    simp only [Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | omega | ring
  simp only [hid, sum_add_distrib, sum_ite_eq', mem_univ, if_true, pow_succ]
  ring

theorem profileMarkedJoint_row (σ : ℝ) (s : ℕ) (i : Fin s) :
    ∑ j, profileMarkedJoint σ s i j = σ ^ s * profileConditional σ s i := by
  simp only [profileMarkedJoint, ← mul_sum]
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, if_true]
  rw [profileMark_sum, mul_comm]

theorem profileMark_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (s : ℕ) (z : Fin (s + 2)) : 0 ≤ profileMark σ s z := by
  unfold profileMark
  split_ifs <;> positivity

theorem profileMark_le {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (s : ℕ) (z : Fin (s + 2)) : profileMark σ s z ≤ profileBinomial σ (s + 1) z := by
  unfold profileMark
  split_ifs with hz hz'
  · simp only [hz, profileBinomial, Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel_left, pow_one]
    have hq : 0 ≤ σ ^ s * (1 - σ) := mul_nonneg (pow_nonneg hσ _) (by linarith)
    nlinarith [mul_nonneg (Nat.cast_nonneg s : (0 : ℝ) ≤ s) hq]
  · simp only [hz', profileBinomial_top, le_refl]
  · exact profileBinomial_nonneg hσ hσ1 _ _

theorem profileMarkedJoint_nonneg {σ : ℝ} {s : ℕ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s) (i : Fin s) (j : Fin (2 * s + 1)) :
    0 ≤ profileMarkedJoint σ s i j := by
  apply mul_nonneg (profileConditional_pos hσ hσ1 hs i).le
  apply sum_nonneg
  intro z _
  split_ifs
  · exact profileMark_nonneg hσ.le hσ1.le s z
  · rfl

theorem profileMarkedJoint_le {σ : ℝ} {s : ℕ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s) (i : Fin s) (j : Fin (2 * s + 1)) :
    profileMarkedJoint σ s i j ≤ profileJoint σ s i j := by
  apply mul_le_mul_of_nonneg_left _ (profileConditional_pos hσ hσ1 hs i).le
  apply sum_le_sum
  intro z _
  split_ifs
  · exact profileMark_le hσ.le hσ1.le s z
  · rfl

theorem profileJoint_pos {σ : ℝ} {s : ℕ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s) (i : Fin s) (j : Fin (2 * s + 1))
    (hlo : (i : ℕ) ≤ j) (hhi : (j : ℕ) ≤ i + s + 1) : 0 < profileJoint σ s i j := by
  apply mul_pos (profileConditional_pos hσ hσ1 hs i)
  let z : Fin (s + 2) := ⟨j - i, by omega⟩
  have hz : profileShift i z = j := by apply Fin.ext; dsimp [profileShift, z]; omega
  apply sum_pos'
  · intro x _
    split_ifs
    · exact profileBinomial_nonneg hσ.le hσ1.le _ _
    · rfl
  · exact ⟨z, mem_univ z, by rw [if_pos hz]; exact profileBinomial_pos hσ hσ1 (by omega)⟩

theorem profileJoint_zero {σ : ℝ} {s : ℕ} (i : Fin s) (j : Fin (2 * s + 1))
    (h : ¬((i : ℕ) ≤ j ∧ (j : ℕ) ≤ i + s + 1)) : profileJoint σ s i j = 0 := by
  unfold profileJoint
  rw [show (∑ z : Fin (s + 2), if profileShift i z = j then profileBinomial σ (s + 1) z else 0) = 0 from ?_]
  · exact mul_zero _
  · apply sum_eq_zero
    intro z _
    rw [if_neg]
    intro hz
    have := congrArg Fin.val hz
    dsimp only [profileShift] at this
    exact h ⟨by omega, by omega⟩

theorem profileMarkedJoint_pos_of_shift {σ : ℝ} {s : ℕ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s)
    (i : Fin s) (z : Fin (s + 2)) (hz : (z : ℕ) = s ∨ (z : ℕ) = s + 1) :
    0 < profileMarkedJoint σ s i (profileShift i z) := by
  apply mul_pos (profileConditional_pos hσ hσ1 hs i)
  apply sum_pos'
  · intro x _
    split_ifs
    · exact profileMark_nonneg hσ.le hσ1.le _ _
    · rfl
  · refine ⟨z, mem_univ z, ?_⟩
    rw [if_pos rfl]
    unfold profileMark
    rcases hz with hz | hz
    · rw [if_pos hz]
      exact mul_pos (pow_pos hσ _) (by linarith)
    · rw [if_neg (by omega), if_pos hz]
      exact pow_pos hσ _

theorem profileMarkedJoint_positive_column {σ : ℝ} {s : ℕ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s) (j : Fin (2 * s + 1)) (hj : s ≤ (j : ℕ)) :
    ∃ i : Fin s, 0 < profileMarkedJoint σ s i j := by
  by_cases htop : (j : ℕ) < 2 * s
  · let i : Fin s := ⟨j - s, by omega⟩
    let z : Fin (s + 2) := ⟨s, by omega⟩
    have heq : profileShift i z = j := by apply Fin.ext; dsimp [profileShift, i, z]; omega
    refine ⟨i, ?_⟩
    rw [← heq]
    exact profileMarkedJoint_pos_of_shift hσ hσ1 hs i z (Or.inl rfl)
  · let i : Fin s := ⟨s - 1, by omega⟩
    let z : Fin (s + 2) := ⟨s + 1, by omega⟩
    have heq : profileShift i z = j := by apply Fin.ext; dsimp [profileShift, i, z]; omega
    refine ⟨i, ?_⟩
    rw [← heq]
    exact profileMarkedJoint_pos_of_shift hσ hσ1 hs i z (Or.inr rfl)

theorem profileMarkedJoint_zero_column {σ : ℝ} {s : ℕ}
    (i : Fin s) (j : Fin (2 * s + 1)) (hj : (j : ℕ) < s) : profileMarkedJoint σ s i j = 0 := by
  unfold profileMarkedJoint
  rw [show (∑ z : Fin (s + 2), if profileShift i z = j then profileMark σ s z else 0) = 0 from ?_]
  · exact mul_zero _
  · apply sum_eq_zero
    intro z _
    split_ifs with hz
    · have hval := congrArg Fin.val hz
      dsimp only [profileShift] at hval
      unfold profileMark
      rw [if_neg (by omega), if_neg (by omega)]
    · rfl

end Froberg
