import Froberg.BinomialPolynomial

/-! Exact integer selection for Section 5. These lemmas establish the count
identity and the precise one-step rounding error used in Proposition 5.1. -/
namespace Froberg

/-- A positive-degree homogeneous component has at least one pure-power
monomial for each variable, expressed by its exact binomial count. -/
theorem variables_le_monomial_count (v t : ℕ) (ht : 0 < t) :
    v ≤ (v + t - 1).choose t := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  induction v with
  | zero => exact Nat.zero_le _
  | succ v ih =>
      have hpos : 1 ≤ (v + t).choose t := Nat.choose_pos (by omega)
      have heq : (v + 1 + (t + 1) - 1) = (v + t) + 1 := by omega
      rw [heq, Nat.choose_succ_succ]
      have hsub : v + (t + 1) - 1 = v + t := by omega
      rw [hsub] at ih
      omega

theorem monomial_count_step (a t : ℕ) (ht : 0 < t) :
    (a + 1 + t - 1).choose t =
      (a + t - 1).choose t + (a + 1 + (t - 1) - 1).choose (t - 1) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  have h₁ : a + 1 + (t + 1) - 1 = a + t + 1 := by omega
  have h₂ : a + (t + 1) - 1 = a + t := by omega
  have h₃ : a + 1 + (t + 1 - 1) - 1 = a + t := by omega
  rw [h₁, h₂, h₃, Nat.succ_sub_one, Nat.choose_succ_succ, Nat.add_comm]

/-- The first index exceeding a budget supplies the preceding admissible index. -/
theorem exists_step_straddle (F : ℕ → ℕ) (B : ℕ)
    (hzero : F 0 ≤ B) (hunbounded : ∃ v, B < F v) :
    ∃ a, F a ≤ B ∧ B < F (a + 1) := by
  classical
  let v := Nat.find hunbounded
  have hv : B < F v := Nat.find_spec hunbounded
  have hvpos : 0 < v := by
    by_contra h
    have hz : v = 0 := by omega
    rw [hz] at hv
    omega
  refine ⟨v - 1, ?_, ?_⟩
  · have hmin := Nat.find_min hunbounded (show v - 1 < Nat.find hunbounded by
      change v - 1 < v
      omega)
    omega
  · simpa only [Nat.sub_add_cancel hvpos] using hv

/-- Select the outer multiplicity exactly, leaving a residual count in an
interval whose width is one binomial step. No asymptotic statement is used. -/
theorem exists_exact_generator_count (K R emin t : ℕ)
    (hK : 0 < K) (ht : 0 < t) (hmin : emin ≤ R) :
    ∃ a f e : ℕ,
      f = K * (a + t - 1).choose t ∧ f + e = R ∧ emin ≤ e ∧
      e < emin + K * (a + 1 + (t - 1) - 1).choose (t - 1) := by
  let F : ℕ → ℕ := fun a => K * (a + t - 1).choose t
  have hzero : F 0 ≤ R - emin := by
    simp [F, Nat.choose_eq_zero_of_lt (show t - 1 < t by omega)]
  have hunbounded : ∃ v, R - emin < F v := by
    refine ⟨R - emin + 1, ?_⟩
    have hc := variables_le_monomial_count (R - emin + 1) t ht
    have hk : 1 ≤ K := hK
    dsimp only [F]
    nlinarith
  obtain ⟨a, ha, hnext⟩ := exists_step_straddle F (R - emin) hzero hunbounded
  refine ⟨a, F a, R - F a, rfl, ?_, ?_, ?_⟩
  · omega
  · omega
  · have hstep : F (a + 1) = F a +
        K * (a + 1 + (t - 1) - 1).choose (t - 1) := by
      dsimp only [F]
      rw [monomial_count_step a t ht, Nat.mul_add]
    omega

end Froberg
