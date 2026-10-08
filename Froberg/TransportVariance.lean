import Mathlib

/-! Finite weighted variance and the mixing estimate used for strict
outer-module shadows. All identities concern explicit finite sums. -/
noncomputable section
namespace Froberg
open Finset
variable {I J : Type*} [Fintype I] [Fintype J]

def weightedMean (p u : I → ℝ) : ℝ := ∑ i, p i * u i
def weightedVariance (p u : I → ℝ) : ℝ := ∑ i, p i * (u i - weightedMean p u) ^ 2

theorem weighted_center_square (p u : I → ℝ) (hp : ∑ i, p i = 1) (z : ℝ) :
    (∑ i, p i * (u i - z) ^ 2) = (∑ i, p i * u i ^ 2) - 2 * z * weightedMean p u + z ^ 2 := by
  calc
    _ = ∑ i, (p i * u i ^ 2 - 2 * z * (p i * u i) + z ^ 2 * p i) := by
      apply sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, hp, mul_one, weightedMean]

theorem weightedVariance_expanded (p u : I → ℝ) (hp : ∑ i, p i = 1) :
    weightedVariance p u = (∑ i, p i * u i ^ 2) - weightedMean p u ^ 2 := by
  rw [weightedVariance, weighted_center_square p u hp]
  ring

theorem weightedVariance_nonneg (p u : I → ℝ) (hp : ∀ i, 0 ≤ p i) :
    0 ≤ weightedVariance p u := sum_nonneg fun i _ => mul_nonneg (hp i) (sq_nonneg _)

theorem weightedVariance_le_centered (p u : I → ℝ) (hp : ∑ i, p i = 1) (z : ℝ) :
    weightedVariance p u ≤ ∑ i, p i * (u i - z) ^ 2 := by
  rw [weightedVariance_expanded p u hp, weighted_center_square p u hp]
  nlinarith [sq_nonneg (weightedMean p u - z)]

theorem weightedVariance_pairwise (p u : I → ℝ) (hp : ∑ i, p i = 1) :
    (∑ i, ∑ j, p i * p j * (u i - u j) ^ 2) = 2 * weightedVariance p u := by
  have hid (i j : I) : p i * p j * (u i - u j) ^ 2 =
      (p i * u i ^ 2) * p j + p i * (p j * u j ^ 2) -
        2 * (p i * u i) * (p j * u j) := by ring
  simp_rw [hid]
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← sum_mul, hp, mul_one, one_mul]
  rw [weightedVariance_expanded p u hp]
  unfold weightedMean
  ring

theorem averaged_center_lower_bound (p q u : I → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) (hqpos : ∀ i, 0 ≤ q i) :
    weightedVariance p u ≤ ∑ i, ∑ j, p i * q j * (u i - u j) ^ 2 := by
  calc
    weightedVariance p u = ∑ j, q j * weightedVariance p u := by rw [← sum_mul, hq, one_mul]
    _ ≤ ∑ j, q j * ∑ i, p i * (u i - u j) ^ 2 := by
      exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (weightedVariance_le_centered p u hp _) (hqpos j)
    _ = _ := by
      rw [sum_comm]
      simp only [mul_sum]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring

def reversibleWeights (ν : J → ℝ) (C : J → I → ℝ) (i k : I) : ℝ :=
  ∑ j, ν j * C j i * C j k

theorem conditional_variance_pairwise (ν : J → ℝ) (C : J → I → ℝ) (u : I → ℝ)
    (hC : ∀ j, ∑ i, C j i = 1) :
    (∑ i, ∑ k, reversibleWeights ν C i k * (u i - u k) ^ 2) =
      2 * ∑ j, ν j * weightedVariance (C j) u := by
  simp only [reversibleWeights, sum_mul]
  calc
    _ = ∑ i, ∑ j, ∑ k, ν j * C j i * C j k * (u i - u k) ^ 2 := by
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = ∑ j, ∑ i, ∑ k, ν j * C j i * C j k * (u i - u k) ^ 2 := sum_comm
    _ = ∑ j, ν j * ∑ i, ∑ k, C j i * C j k * (u i - u k) ^ 2 := by
      apply sum_congr rfl
      intro j _
      simp only [mul_sum]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro k _
      ring
    _ = _ := by
      simp only [weightedVariance_pairwise _ _ (hC _)]
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring

theorem conditional_variance_mixing (ν : J → ℝ) (C : J → I → ℝ) (p q u : I → ℝ)
    (hC : ∀ j, ∑ i, C j i = 1) (hp : ∑ i, p i = 1)
    (hq : ∑ i, q i = 1) (hqpos : ∀ i, 0 ≤ q i) (κ : ℝ) (hκ : 0 ≤ κ)
    (hminor : ∀ i k, κ * p i * q k ≤ reversibleWeights ν C i k) :
    κ / 2 * weightedVariance p u ≤ ∑ j, ν j * weightedVariance (C j) u := by
  have hpoint : κ * (∑ i, ∑ k, p i * q k * (u i - u k) ^ 2) ≤
      ∑ i, ∑ k, reversibleWeights ν C i k * (u i - u k) ^ 2 := by
    simp only [mul_sum]
    apply sum_le_sum
    intro i _
    apply sum_le_sum
    intro k _
    have hh := mul_le_mul_of_nonneg_right (hminor i k) (sq_nonneg (u i - u k))
    convert hh using 1 <;> ring
  rw [conditional_variance_pairwise ν C u hC] at hpoint
  have hlow := mul_le_mul_of_nonneg_left (averaged_center_lower_bound p q u hp hq hqpos) hκ
  nlinarith

end Froberg
