import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! Exact finite binomial mass retained in the scalar separation of B.4. -/
namespace Froberg
open Finset

/-- Pascal's identity propagates the degree-nine maximum coefficient bound. -/
theorem binomial_coefficient_le_sixty_three {d : ℕ} (hd : 9 ≤ d) (u : ℕ) :
    256 * d.choose u ≤ 63 * 2 ^ d := by
  induction d, hd using Nat.le_induction generalizing u with
  | base =>
    by_cases hu : u ≤ 9
    · interval_cases u <;> norm_num [Nat.choose_eq_factorial_div_factorial]
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      omega
  | succ d hd ih =>
    cases u with
    | zero =>
      have h := ih 0
      simp only [Nat.choose_zero_right] at h ⊢
      rw [pow_succ]
      omega
    | succ u =>
      rw [Nat.choose_succ_succ, pow_succ]
      have h₁ := ih u
      have h₂ := ih (u+1)
      simp only [Nat.succ_eq_add_one] at *
      omega

def parityBinomialIndices (d i p : ℕ) : Finset ℕ :=
  (range (d+1)).filter (fun u => (i+u)%2 ≠ p)

theorem parity_binomial_mass_succ (n i p : ℕ) (hp : p < 2) :
    ∑ u ∈ parityBinomialIndices (n+1) i p, (n+1).choose u = 2 ^ n := by
  let f : ℕ → ℕ → ℕ := fun u _ => if (i+u)%2 ≠ p then 1 else 0
  calc
    _ = ∑ u ∈ range (n+2), (n+1).choose u * f u (n+1-u) := by
      simp only [parityBinomialIndices, sum_filter, f, mul_ite, mul_one, mul_zero]
    _ = (∑ u ∈ range (n+1), n.choose u * f u (n+1-u)) +
        ∑ u ∈ range (n+1), n.choose u * f (u+1) (n-u) := Finset.sum_choose_succ_mul f n
    _ = ∑ u ∈ range (n+1), n.choose u := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro u hu
      rw [← Nat.mul_add]
      have hpair : f u (n+1-u) + f (u+1) (n-u) = 1 := by
        dsimp only [f]
        split_ifs <;> omega
      rw [hpair, Nat.mul_one]
    _ = 2^n := Nat.sum_range_choose n

theorem parity_binomial_mass {d : ℕ} (hd : 0<d) (i p : ℕ) (hp : p<2) :
    ∑ u ∈ parityBinomialIndices d i p, d.choose u = 2^(d-1) := by
  cases d with
  | zero => omega
  | succ n => simpa using parity_binomial_mass_succ n i p hp

/-- Removing one total degree from either parity loses at most one binomial coefficient. -/
theorem parity_binomial_mass_except_le (d i p j : ℕ) :
    ∑ u ∈ parityBinomialIndices d i p, d.choose u ≤
      (∑ u ∈ (parityBinomialIndices d i p).filter (fun u => i+u ≠ j), d.choose u) +
        d.choose (j-i) := by
  let S := parityBinomialIndices d i p
  have hsub : S.erase (j-i) ⊆ S.filter (fun u => i+u ≠ j) := by
    intro u hu
    obtain ⟨hne, hmem⟩ := mem_erase.mp hu
    exact mem_filter.mpr ⟨hmem, by omega⟩
  have hle : (∑ u ∈ S.erase (j-i), d.choose u) ≤
      ∑ u ∈ S.filter (fun u => i+u ≠ j), d.choose u :=
    sum_le_sum_of_subset hsub
  change (∑ u ∈ S, d.choose u) ≤
    (∑ u ∈ S.filter (fun u => i+u ≠ j), d.choose u) + d.choose (j-i)
  by_cases hm : j-i ∈ S
  · have heq := sum_erase_add S (fun u => d.choose u) hm
    omega
  · rw [erase_eq_of_notMem hm] at hle
    omega

/-- The exact uniform `65/256` mass estimate used in B.4. -/
theorem parity_binomial_mass_except_margin {d : ℕ} (hd : 9≤d)
    (i p j : ℕ) (hp : p<2) :
    65 * 2^d ≤ 256 *
      (∑ u ∈ (parityBinomialIndices d i p).filter (fun u => i+u ≠ j), d.choose u) := by
  have hmass := parity_binomial_mass (by omega : 0<d) i p hp
  have hremove := parity_binomial_mass_except_le d i p j
  have hcoeff := binomial_coefficient_le_sixty_three hd (j-i)
  have hpow : 2^d = 2 * 2^(d-1) := by
    calc
      2^d = 2^((d-1)+1) := by congr 1; omega
      _ = 2 * 2^(d-1) := by rw [pow_succ]; omega
  omega

end Froberg
