import Froberg.ProfileTransport

/-! Identification of the explicit transport's target marginal with the
coarse quotient capacities in Theorem B.2. -/
noncomputable section
namespace Froberg
open Polynomial Finset

theorem profileJoint_polynomial (σ : ℝ) (s : ℕ) (i : Fin s) (j : Fin (2 * s + 1)) :
    profileJoint σ s i j = profileConditional σ s i *
      (X ^ (i : ℕ) * profilePolynomial σ (s + 1)).coeff j := by
  unfold profileJoint
  congr 1
  rw [coeff_X_pow_mul']
  by_cases hlo : (i : ℕ) ≤ j
  · rw [if_pos hlo, profilePolynomial_coeff]
    by_cases hhi : (j : ℕ) - i ≤ s + 1
    · let z : Fin (s + 2) := ⟨j - i, by omega⟩
      have hz : profileShift i z = j := by apply Fin.ext; dsimp [profileShift, z]; omega
      rw [sum_eq_single z]
      · rw [if_pos hz]
      · intro x _ hx
        rw [if_neg]
        intro heq
        exact hx (profileShift_injective i (heq.trans hz.symm))
      · intro hx
        exact False.elim (hx (mem_univ z))
    · rw [profileBinomial_above σ (by omega : s + 1 < (j : ℕ) - i)]
      apply sum_eq_zero
      intro z _
      rw [if_neg]
      intro hz
      have := congrArg Fin.val hz
      dsimp only [profileShift] at this
      omega
  · rw [if_neg hlo]
    apply sum_eq_zero
    intro z _
    rw [if_neg]
    intro hz
    have := congrArg Fin.val hz
    dsimp only [profileShift] at this
    omega

theorem profileTargetMass_polynomial (σ : ℝ) (s : ℕ) (j : Fin (2 * s + 1)) :
    profileTargetMass σ s j =
      ((profilePolynomial σ s - monomial s (σ ^ s)) *
        profilePolynomial σ (s + 1)).coeff j / (1 - σ ^ s) := by
  rw [← profilePolynomial_truncated]
  simp only [sum_mul, finsetSum_coeff, sum_div, profileTargetMass,
    profileJoint_polynomial, profileConditional]
  apply sum_congr rfl
  intro i _
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul]
  ring

theorem profileTargetMass_formula (σ : ℝ) (s : ℕ) (j : Fin (2 * s + 1)) :
    profileTargetMass σ s j = (profileBinomial σ (2 * s + 1) j -
      if s ≤ (j : ℕ) then σ ^ s * profileBinomial σ (s + 1) ((j : ℕ) - s) else 0) /
      (1 - σ ^ s) := by
  rw [profileTargetMass_polynomial, sub_mul, coeff_sub]
  have hpow : profilePolynomial σ s * profilePolynomial σ (s + 1) =
      profilePolynomial σ (2 * s + 1) := by
    simp only [profilePolynomial, ← pow_add]
    congr 1
    omega
  rw [hpow, profilePolynomial_coeff, ← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul', profilePolynomial_coeff]
  split_ifs <;> simp_all

theorem weighted_choose_subtract {σ : ℝ} (s j : ℕ) (hsj : s ≤ j) (hjn : j ≤ 2 * s + 1) :
    (((2 * s + 1).choose s : ℕ) : ℝ) * σ ^ s * profileBinomial σ (s + 1) (j - s) =
      (j.choose s : ℝ) * profileBinomial σ (2 * s + 1) j := by
  have hc : (((2 * s + 1).choose j : ℕ) : ℝ) * (j.choose s : ℝ) =
      (((2 * s + 1).choose s : ℕ) : ℝ) * ((s + 1).choose (j - s) : ℝ) := by
    have ht := Nat.choose_mul (n := 2 * s + 1) hsj
    have hh : 2 * s + 1 - s = s + 1 := by omega
    rw [hh] at ht
    exact_mod_cast ht
  have h₁ : s + (j - s) = j := by omega
  have h₂ : s + 1 - (j - s) = 2 * s + 1 - j := by omega
  unfold profileBinomial
  rw [h₂]
  calc
    _ = ((((2 * s + 1).choose s : ℕ) : ℝ) * ((s + 1).choose (j - s) : ℝ)) *
        (σ ^ s * σ ^ (j - s)) * (1 - σ) ^ (2 * s + 1 - j) := by ring
    _ = _ := by rw [← hc, ← pow_add, h₁]; ring

theorem profileTargetMass_capacity (σ : ℝ) (s : ℕ) (j : Fin (2 * s + 1)) :
    profileTargetMass σ s j =
      ((((2 * s + 1).choose s : ℕ) : ℝ) - (j.val.choose s : ℝ)) *
        profileBinomial σ (2 * s + 1) j /
        ((((2 * s + 1).choose s : ℕ) : ℝ) * (1 - σ ^ s)) := by
  have hH : ((((2 * s + 1).choose s : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : s ≤ 2 * s + 1)))
  rw [profileTargetMass_formula]
  by_cases hsj : s ≤ (j : ℕ)
  · rw [if_pos hsj]
    have hw := weighted_choose_subtract (σ := σ) s j hsj (by omega)
    by_cases hσ : 1 - σ ^ s = 0
    · simp [hσ]
    · field_simp
      nlinarith [hw]
  · rw [if_neg hsj, Nat.choose_eq_zero_of_lt (by omega : (j : ℕ) < s)]
    simp only [Nat.cast_zero, sub_zero]
    field_simp

end Froberg
