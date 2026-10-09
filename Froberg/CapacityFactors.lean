module

public import Froberg.CapacityFactorials

@[expose] public section

/-! # Separated factorial factors in the higher scalar ratios -/

noncomputable section
namespace Froberg

def scalarLeftFactor (j : ℕ) : ℝ :=
  ((j - 4).factorial : ℝ) * (j.factorial : ℝ) / ((2 * j - 4).factorial : ℝ)

def scalarRightFactor (d t : ℕ) : ℝ :=
  ((t + 4).factorial : ℝ) * ((d + t).factorial : ℝ) /
    (((2 * t + 4).factorial : ℝ) * (d.factorial : ℝ))

theorem factorial_real_ne_zero (m : ℕ) : (m.factorial : ℝ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero m

theorem higher_scalar_factorization {d j : ℕ} (hj : 6 ≤ j) (hjd : j ≤ d) :
    higherCountGamma d j / scalarCapacity d j = scalarLeftFactor j * scalarRightFactor d (d - j) := by
  have h₁ : 2 * d - 2 * j + 4 = 2 * (d - j) + 4 := by omega
  have h₂ : 2 * d - j = d + (d - j) := by omega
  simp only [higherCountGamma, if_neg (by omega : j ≠ 4), scalarCapacity,
    scalarLeftFactor, scalarRightFactor, h₁, h₂]
  field_simp [factorial_real_ne_zero] <;> ring

theorem scalarLeftFactor_pos {j : ℕ} : 0 < scalarLeftFactor j := by
  unfold scalarLeftFactor
  positivity

theorem scalarRightFactor_pos {d t : ℕ} : 0 < scalarRightFactor d t := by
  unfold scalarRightFactor
  positivity

theorem scalarLeftFactor_step {j : ℕ} (hj : 6 ≤ j) :
    scalarLeftFactor (j + 1) = scalarLeftFactor j *
      (((j : ℝ) + 1) * ((j : ℝ) - 3) /
        ((2 * (j : ℝ) - 2) * (2 * (j : ℝ) - 3))) := by
  have h₁ := factorial_pred_real (m := j - 3) (by omega)
  rw [show j - 3 - 1 = j - 4 by omega, Nat.cast_sub (by omega : 3 ≤ j), Nat.cast_ofNat] at h₁
  have h₂ := factorial_two_pred_real (m := 2 * j - 2) (by omega)
  rw [show 2 * j - 2 - 2 = 2 * j - 4 by omega,
    Nat.cast_sub (by omega : 2 ≤ 2 * j), Nat.cast_mul, Nat.cast_ofNat] at h₂
  have h₃ : ((j + 1).factorial : ℝ) = ((j : ℝ) + 1) * (j.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hj2 : 2 * (j : ℝ) - 2 ≠ 0 := by
    have : (6 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have hj3 : 2 * (j : ℝ) - 3 ≠ 0 := by
    have : (6 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  unfold scalarLeftFactor
  rw [show j + 1 - 4 = j - 3 by omega,
    show 2 * (j + 1) - 4 = 2 * j - 2 by omega, h₁, h₂, h₃]
  field_simp [factorial_real_ne_zero, hj2, hj3] <;> ring

theorem factorial_add_one_real (n : ℕ) :
    ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
  rw [Nat.factorial_succ]
  push_cast
  ring

theorem factorial_add_two_real (n : ℕ) :
    ((n + 2).factorial : ℝ) = ((n : ℝ) + 2) * ((n : ℝ) + 1) * (n.factorial : ℝ) := by
  rw [show n + 2 = (n + 1) + 1 by omega, factorial_add_one_real, factorial_add_one_real]
  push_cast
  ring

theorem scalarRightFactor_step (d t : ℕ) :
    scalarRightFactor d t = scalarRightFactor d (t + 1) *
      (((2 * (t : ℝ) + 6) * (2 * (t : ℝ) + 5)) /
        (((t : ℝ) + 5) * ((d : ℝ) + (t : ℝ) + 1))) := by
  have h₁ : t + 1 + 4 = (t + 4) + 1 := by omega
  have h₂ : d + (t + 1) = (d + t) + 1 := by omega
  have h₃ : 2 * (t + 1) + 4 = (2 * t + 4) + 2 := by omega
  unfold scalarRightFactor
  rw [h₁, h₂, h₃, factorial_add_one_real (t + 4),
    factorial_add_one_real (d + t), factorial_add_two_real (2 * t + 4)]
  push_cast
  have ht5 : (t : ℝ) + 5 ≠ 0 := by positivity
  have hdt : (d : ℝ) + (t : ℝ) + 1 ≠ 0 := by positivity
  field_simp [factorial_real_ne_zero, ht5, hdt] <;> ring

end Froberg
