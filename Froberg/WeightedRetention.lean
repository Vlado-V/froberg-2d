import Froberg.WeightedExpansion

/-! Weighted counting after deleting target coordinates. -/
namespace Froberg
open Finset

/-- A rational lower bound on the weight retained by every source gives the
same lower bound on the weighted size of the retained target. -/
theorem weighted_retention_bound {S T : Type*} [DecidableEq S] [DecidableEq T]
    (w : T → S → ℕ) (A : Finset S) (B : Finset T) (a b L C : ℕ)
    (hsource : ∀ s ∈ A, a * L ≤ b * ∑ t ∈ B, w t s)
    (htarget : ∀ t ∈ B, ∑ s ∈ A, w t s ≤ C) :
    a * L * A.card ≤ b * C * B.card := by
  calc
    a * L * A.card = ∑ s ∈ A, a * L := by simp [Nat.mul_comm]
    _ ≤ ∑ s ∈ A, b * ∑ t ∈ B, w t s := sum_le_sum hsource
    _ = b * ∑ t ∈ B, ∑ s ∈ A, w t s := by rw [← mul_sum, sum_comm]
    _ ≤ b * ∑ t ∈ B, C := Nat.mul_le_mul_left b (sum_le_sum htarget)
    _ = b * C * B.card := by simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- The total-weight identity converts a retained-weight bound into the
normalized dimension inequality, without introducing rational divisions. -/
theorem normalized_retention_bound (N T k B a b L C : ℕ)
    (hC : 0 < C) (htotal : N * L = C * T)
    (hretained : a * L * k ≤ b * C * B) :
    a * T * k ≤ b * N * B := by
  have h := Nat.mul_le_mul_left N hretained
  have he : N * (a * L * k) = C * (a * T * k) := by
    calc
      N * (a * L * k) = a * k * (N * L) := by ring
      _ = a * k * (C * T) := by rw [htotal]
      _ = C * (a * T * k) := by ring
  rw [he] at h
  have he' : N * (b * C * B) = C * (b * N * B) := by ring
  rw [he'] at h
  exact Nat.le_of_mul_le_mul_left h hC

end Froberg
