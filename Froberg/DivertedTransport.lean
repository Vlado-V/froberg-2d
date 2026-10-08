import Mathlib

/-! A constructive positive transport obtained by diverting a marked part
of each row to one new row. This is the finite transport used for the core
profiles of the outer module. -/
noncomputable section
namespace Froberg
open Finset
variable {I J : Type*} [Fintype I] [Fintype J]

def divertedTransport (P D : I → J → ℝ) (t : ℝ) : Option I → J → ℝ
  | some i, j => P i j - t * D i j
  | none, j => t * ∑ i, D i j

theorem divertedTransport_column (P D : I → J → ℝ) (t : ℝ) (j : J) :
    ∑ i, divertedTransport P D t i j = ∑ i, P i j := by
  simp only [Fintype.sum_option, divertedTransport, sum_sub_distrib, ← mul_sum]
  ring

theorem divertedTransport_old_row (P D : I → J → ℝ) (a : I → ℝ) (p t : ℝ)
    (hP : ∀ i, ∑ j, P i j = a i) (hD : ∀ i, ∑ j, D i j = p * a i) (i : I) :
    ∑ j, divertedTransport P D t (some i) j = (1 - t * p) * a i := by
  simp only [divertedTransport, sum_sub_distrib, ← mul_sum, hP, hD]
  ring

theorem divertedTransport_new_row (P D : I → J → ℝ) (a : I → ℝ) (p t : ℝ)
    (ha : ∑ i, a i = 1) (hD : ∀ i, ∑ j, D i j = p * a i) :
    ∑ j, divertedTransport P D t none j = t * p := by
  simp only [divertedTransport, ← mul_sum]
  rw [sum_comm]
  simp only [hD, ← mul_sum, ha, mul_one]

theorem divertedTransport_nonneg (P D : I → J → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hD : ∀ i j, 0 ≤ D i j) (hDP : ∀ i j, D i j ≤ P i j) :
    ∀ i j, 0 ≤ divertedTransport P D t i j := by
  intro i j
  cases i with
  | none => exact mul_nonneg ht (sum_nonneg fun i _ => hD i j)
  | some i =>
      have hh := mul_le_mul_of_nonneg_right ht1 (hD i j)
      dsimp only [divertedTransport]
      linarith [hDP i j]

theorem divertedTransport_old_pos (P D : I → J → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t < 1) (i : I) (j : J)
    (hP : 0 < P i j) (hD : 0 ≤ D i j) (hDP : D i j ≤ P i j) :
    0 < divertedTransport P D t (some i) j := by
  have h₁ := mul_le_mul_of_nonneg_left hDP ht
  have h₂ := mul_lt_mul_of_pos_right ht1 hP
  dsimp only [divertedTransport]
  linarith

theorem divertedTransport_new_pos (P D : I → J → ℝ) (t : ℝ)
    (ht : 0 < t) (hD : ∀ i j, 0 ≤ D i j) (j : J)
    (hj : ∃ i, 0 < D i j) :
    0 < divertedTransport P D t none j := by
  apply mul_pos ht
  obtain ⟨i, hi⟩ := hj
  exact sum_pos' (fun k _ => hD k j) ⟨i, mem_univ i, hi⟩

theorem divertedTransport_zero (P D : I → J → ℝ) (t : ℝ) (i : I) (j : J)
    (hP : P i j = 0) (hD : D i j = 0) :
    divertedTransport P D t (some i) j = 0 := by
  simp only [divertedTransport, hP, hD, mul_zero, sub_zero]

end Froberg
