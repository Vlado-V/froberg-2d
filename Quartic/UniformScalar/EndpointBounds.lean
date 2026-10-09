module

public import Quartic.UniformEndpoint

@[expose] public section

/-! Sharper exact endpoint bounds used by the all-dimension scalar argument. -/

namespace Quartic.UniformScalar

open Quartic.Counts Quartic.UniformEndpoint

/-- Evaluation at any fixed offset from the quadratic root approximation. -/
theorem eulerReal_base_offset (n e : ℝ) :
    eulerReal n (baseCount n + e) =
      (1 / 3 - rho / 2 + e * (rho - 1 / 2)) * n^2 + (e^2 - e) / 2 := by
  unfold eulerReal baseCount
  linear_combination (n^4 / 24) * rho_identity

/-- A fixed rational bracket suffices in every dimension at least three. -/
theorem upper_endpoint_tight (n : ℕ) (hn : 3 ≤ n) :
    baseCount n + 2 / 3 < (upperEndpoint n : ℝ) ∧
      (upperEndpoint n : ℝ) < baseCount n + 7 / 4 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hn2 : (9 : ℝ) ≤ (n : ℝ)^2 := by nlinarith
  have hr := rho_bounds
  have hlow := mul_nonneg (sub_nonneg.mpr hr.1) (sq_nonneg (n : ℝ))
  have hupp := mul_nonneg (sub_nonneg.mpr hr.2) (sq_nonneg (n : ℝ))
  have hbasepos : 0 < eulerReal n (baseCount n + 2 / 3) := by
    rw [eulerReal_base_offset]
    nlinarith only [hlow, hn2]
  have hbaseneg : eulerReal n (baseCount n + 3 / 4) < 0 := by
    rw [eulerReal_base_offset]
    nlinarith only [hupp, hn2]
  have hbasequad : baseCount n + 2 / 3 ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    unfold baseCount
    nlinarith only [hupp, hn2]
  have hqnonpos : eulerReal n (upperEndpoint n) ≤ 0 := by
    rw [← chi_cast]
    exact_mod_cast upper_nonpositive n
  have hquad : (upperEndpoint n : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    have hu : (upperEndpoint n : ℝ) ≤ (b2 n : ℝ) := by
      simp only [b2, Int.cast_natCast]
      exact_mod_cast upper_le_quadratics n
    have h₂ : 2 * (b2 n : ℝ) = (n : ℝ) * ((n : ℝ) + 1) := by exact_mod_cast b2_scaled n
    linarith
  constructor
  · by_contra h
    have hle : (upperEndpoint n : ℝ) ≤ baseCount n + 2 / 3 := by linarith
    have hmono := eulerReal_antitone n (upperEndpoint n) (baseCount n + 2 / 3) hle hbasequad
    linarith
  · by_contra h
    have hle : baseCount n + 7 / 4 ≤ (upperEndpoint n : ℝ) := by linarith
    have hbpos : 0 < baseCount (n : ℝ) := by
      unfold baseCount
      have hrpos : (0 : ℝ) < rho := by linarith
      positivity
    have hqpos : 0 < upperEndpoint n := by
      have hq : (0 : ℝ) < upperEndpoint n := by linarith
      exact_mod_cast hq
    have hpred : ((upperEndpoint n - 1 : ℕ) : ℝ) = (upperEndpoint n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ upperEndpoint n), Nat.cast_one]
    have hp : 0 < eulerReal n ((upperEndpoint n - 1 : ℕ) : ℝ) := by
      rw [← chi_cast]
      exact_mod_cast before_upper_positive n (upperEndpoint n - 1) (by omega)
    have hmono := eulerReal_antitone n (baseCount n + 3 / 4) ((upperEndpoint n - 1 : ℕ) : ℝ)
      (by rw [hpred]; linarith) (by rw [hpred]; linarith)
    linarith

theorem parent_endpoint_tight (m : ℕ) (upper : Bool) :
    baseCount (m + 3 : ℕ) - 1 / 3 < (parentCount m upper : ℝ) ∧
      (parentCount m upper : ℝ) < baseCount (m + 3 : ℕ) + 7 / 4 := by
  have hq := upper_endpoint_tight (m + 3) (by omega)
  have hadj := lower_upper_adjacent (m + 3)
  have hlo : (lowerEndpoint (m + 3) : ℝ) ≤ (upperEndpoint (m + 3) : ℝ) := by exact_mod_cast hadj.1
  have hhi : (upperEndpoint (m + 3) : ℝ) ≤ (lowerEndpoint (m + 3) : ℝ) + 1 := by exact_mod_cast hadj.2
  cases upper <;> simp only [parentCount, Bool.false_eq_true, ite_false, ite_true] <;>
    constructor <;> linarith

/-- Exact cast of the natural subtraction defining the mixed count. -/
theorem mixedCount_cast (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    (mixedCount m upper : ℝ) = (parentCount m upper : ℝ) - (upperEndpoint m : ℝ) - 4 := by
  have h := parent_ge_child_add_six m hm upper
  unfold mixedCount
  rw [Nat.cast_sub (by omega : 4 ≤ parentCount m upper - upperEndpoint m),
    Nat.cast_sub (by omega : upperEndpoint m ≤ parentCount m upper)]
  norm_num

/-- The precise mixed-count inequalities stated in `sc:count-bounds`, uniformly
for both parent endpoints. Here `tau = 6 rho = 3 - sqrt 6`. -/
theorem mixed_count_bounds (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    6 * rho * (m : ℝ) - 4 < (mixedCount m upper : ℝ) ∧
      (mixedCount m upper : ℝ) < 6 * rho * (m : ℝ) - 1 / 2 := by
  have hq := upper_endpoint_tight m (by omega)
  have hp := parent_endpoint_tight m upper
  have hdiff : baseCount (m + 3 : ℕ) - baseCount m =
      6 * rho * (m : ℝ) + 9 * rho + 3 / 2 := by
    unfold baseCount
    push_cast
    ring
  rw [mixedCount_cast m hm upper]
  have hr := rho_bounds
  constructor <;> linarith

end Quartic.UniformScalar
