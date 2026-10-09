module

public import Froberg.CapacityRatios

@[expose] public section

/-! # Explicit lower bounds two places from the middle binomial coefficient -/

namespace Froberg

def nearCentralBinomial (m : ℕ) : ℕ := (2 * m).choose (m + 2)

theorem nearCentralBinomial_identity (m : ℕ) :
    nearCentralBinomial m * (m + 1) * (m + 2) = Nat.centralBinom m * m * (m - 1) := by
  have h₁ := Nat.choose_succ_right_eq (2 * m) m
  have h₂ := Nat.choose_succ_right_eq (2 * m) (m + 1)
  rw [show 2 * m - m = m by omega] at h₁
  rw [show 2 * m - (m + 1) = m - 1 by omega] at h₂
  have h₁' : (m + 1) * (2 * m).choose (m + 1) = m * Nat.centralBinom m := by
    simpa only [Nat.mul_comm, Nat.centralBinom] using h₁
  have h₂' : (m + 2) * nearCentralBinomial m = (m - 1) * (2 * m).choose (m + 1) := by
    simpa only [Nat.mul_comm, nearCentralBinomial] using h₂
  calc
    nearCentralBinomial m * (m + 1) * (m + 2) =
        ((m + 2) * nearCentralBinomial m) * (m + 1) := by ring
    _ = ((m - 1) * (2 * m).choose (m + 1)) * (m + 1) := by rw [h₂']
    _ = ((m + 1) * (2 * m).choose (m + 1)) * (m - 1) := by ring
    _ = _ := by rw [h₁']; ring

theorem nearCentralBinomial_five {m : ℕ} (hm : 4 ≤ m) :
    2 * Nat.centralBinom m ≤ 5 * nearCentralBinomial m := by
  have hsub : m - 1 + 1 = m := by omega
  have hfour : m - 4 + 4 = m := by omega
  have hp : 2 * ((m + 1) * (m + 2)) ≤ 5 * m * (m - 1) := by
    nlinarith [Nat.zero_le ((m - 4) * (m - 4))]
  apply Nat.le_of_mul_le_mul_right (c := (m + 1) * (m + 2)) _ (by positivity)
  calc
    (2 * Nat.centralBinom m) * ((m + 1) * (m + 2)) =
        Nat.centralBinom m * (2 * ((m + 1) * (m + 2))) := by ring
    _ ≤ Nat.centralBinom m * (5 * m * (m - 1)) := Nat.mul_le_mul_left _ hp
    _ = (5 * nearCentralBinomial m) * ((m + 1) * (m + 2)) := by
      have hi := nearCentralBinomial_identity m
      nlinarith [hi]

theorem nearCentralBinomial_two {m : ℕ} (hm : 6 ≤ m) :
    Nat.centralBinom m ≤ 2 * nearCentralBinomial m := by
  have hsub : m - 1 + 1 = m := by omega
  have hsix : m - 6 + 6 = m := by omega
  have hp : (m + 1) * (m + 2) ≤ 2 * m * (m - 1) := by
    nlinarith [Nat.zero_le ((m - 6) * (m - 6))]
  apply Nat.le_of_mul_le_mul_right (c := (m + 1) * (m + 2)) _ (by positivity)
  calc
    Nat.centralBinom m * ((m + 1) * (m + 2)) ≤
        Nat.centralBinom m * (2 * m * (m - 1)) := Nat.mul_le_mul_left _ hp
    _ = (2 * nearCentralBinomial m) * ((m + 1) * (m + 2)) := by
      have hi := nearCentralBinomial_identity m
      nlinarith [hi]

theorem nearCentralBinomial_exponential_five {m : ℕ} (hm : 4 ≤ m) :
    2 * 4 ^ m ≤ 5 * (2 * m + 1) * nearCentralBinomial m := by
  have h := Nat.four_pow_le_two_mul_add_one_mul_centralBinom m
  have h' := Nat.mul_le_mul_left (2 * m + 1) (nearCentralBinomial_five hm)
  nlinarith

theorem nearCentralBinomial_exponential_two {m : ℕ} (hm : 6 ≤ m) :
    4 ^ m ≤ 2 * (2 * m + 1) * nearCentralBinomial m := by
  have h := Nat.four_pow_le_two_mul_add_one_mul_centralBinom m
  have h' := Nat.mul_le_mul_left (2 * m + 1) (nearCentralBinomial_two hm)
  nlinarith

end Froberg
