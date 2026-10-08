import Quartic.UniformScalar.RealCounts
import Quartic.ProfileCertificate.Core

/-! Infinite-range structural counts in the original integer/binomial notation. -/

namespace Quartic.UniformScalar

open Quartic.Counts Quartic.UniformEndpoint

noncomputable section

theorem b2_cast (n : ℕ) : (b2 n : ℝ) = (n : ℝ)*((n : ℝ)+1)/2 := by
  have h : 2*(b2 n : ℝ) = (n : ℝ)*((n : ℝ)+1) := by exact_mod_cast b2_scaled n
  linarith

theorem b3_cast (n : ℕ) : (b3 n : ℝ) = (n : ℝ)*((n : ℝ)+1)*((n : ℝ)+2)/6 := by
  have h : 6*(b3 n : ℝ) = (n : ℝ)*((n : ℝ)+1)*((n : ℝ)+2) := by exact_mod_cast b3_scaled n
  linarith

theorem pairs_cast (n : ℕ) : (n.choose 2 : ℝ) = (n : ℝ)*((n : ℝ)-1)/2 := by
  have h : 2*(n.choose 2 : ℝ) = (n : ℝ)*((n : ℝ)-1) := by exact_mod_cast choose_two_scaled n
  linarith

theorem alpha_cast (m q : ℕ) : (alpha m q : ℝ) = alphaR m q := by
  simp only [alpha, Int.cast_sub, Int.cast_natCast, b2_cast, alphaR]

theorem beta_cast (m q : ℕ) : (beta m q : ℝ) = betaR m q := by
  simp only [beta, Int.cast_sub, Int.cast_mul, Int.cast_natCast, b3_cast, betaR]

theorem j_cast (m q c : ℕ) : (j m q c : ℝ) = jR m q c := by
  simp only [j, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, beta_cast, alpha_cast, jR]

theorem H_cast (m q c : ℕ) : (H m q c : ℝ) = HR m q c := by
  simp only [H, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
    alpha_cast, pairs_cast, HR]

/-- The canonical endpoint defect bounds hold without a finite dimension cutoff. -/
theorem endpoint_defect (n : ℕ) :
    0 ≤ delta n (upperEndpoint n) ∧ delta n (upperEndpoint n) ≤ alpha n (upperEndpoint n) := by
  have hq : (upperEndpoint n : ℤ) ≤ b2 n := by
    unfold b2
    exact_mod_cast upper_le_quadratics n
  have hb : chi n (upperEndpoint n) = 0 ∨
      ∃ r, upperEndpoint n = r+1 ∧ 0 < chi n r := by
    by_cases hz : chi n (upperEndpoint n) = 0
    · exact Or.inl hz
    · right
      have hpos : 0 < upperEndpoint n := by
        by_contra h
        have hzero : upperEndpoint n = 0 := by omega
        have hnonneg : 0 ≤ chi n (upperEndpoint n) := by
          rw [hzero]
          simp [chi, b4]
        exact hz (le_antisymm (upper_nonpositive n) hnonneg)
      exact ⟨upperEndpoint n-1, by omega, before_upper_positive n _ (by omega)⟩
  simpa only [delta, alpha] using endpoint_defect_bounds_or_root n (upperEndpoint n) hq (upper_nonpositive n) hb

/-- Source column counts are in the valid convolution range, uniformly. -/
theorem c_range (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    4 ≤ mixedCount m upper ∧ mixedCount m upper ≤ m := by
  have hc := (actual_validCounts m hm upper).c_coarse
  exact ⟨by exact_mod_cast hc.2.1, by exact_mod_cast hc.2.2.2⟩

theorem two_c_gt (m : ℕ) (hm : 320 ≤ m) (upper : Bool) : m < 2*mixedCount m upper := by
  have hc := (actual_validCounts m hm upper).c_coarse.1
  have h : (m : ℝ) < 2*(mixedCount m upper : ℝ) := by linarith
  exact_mod_cast h

/-- Every structural inequality in `sc:structural-counts` for all `m≥320`. -/
theorem structural_binomial_counts (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    let q := upperEndpoint m
    let c := mixedCount m upper
    let w₀ := m-2*c
    4 ≤ c ∧ c ≤ m ∧ (m : ℤ)*(q : ℤ) ≤ b3 m ∧
      3 ≤ alpha m q-b2 c ∧ (c : ℤ)*(w₀ : ℤ)+b2 w₀ ≤ (q : ℤ) := by
  have h := actual_validCounts m hm upper
  have hc := c_range m hm upper
  have hβ : (0 : ℝ) < (beta m (upperEndpoint m) : ℝ) := by
    rw [beta_cast]
    exact h.cubic_margin
  have hβi : 0 < beta m (upperEndpoint m) := by exact_mod_cast hβ
  have hprod : (3 : ℝ) ≤ (alpha m (upperEndpoint m) : ℝ)-(b2 (mixedCount m upper) : ℝ) := by
    rw [alpha_cast, b2_cast]
    exact h.product_margin
  have hprodi : 3 ≤ alpha m (upperEndpoint m)-b2 (mixedCount m upper) := by exact_mod_cast hprod
  have hw₀ : m-2*mixedCount m upper = 0 := by have ht := two_c_gt m hm upper; omega
  refine ⟨hc.1, hc.2, ?_, hprodi, ?_⟩
  · unfold beta at hβi
    omega
  · simp only [hw₀]
    norm_num [b2]

/-- All remaining dimension signs in the scalar transfer hypotheses. -/
theorem structural_dimension_signs (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    0 < j m (upperEndpoint m) (mixedCount m upper) ∧
    0 ≤ H m (upperEndpoint m) (mixedCount m upper) ∧
    0 ≤ delta m (upperEndpoint m) ∧ delta m (upperEndpoint m) ≤ alpha m (upperEndpoint m) := by
  have h := actual_validCounts m hm upper
  have hj : (0 : ℝ) < (j m (upperEndpoint m) (mixedCount m upper) : ℝ) := by
    rw [j_cast]
    exact h.j_pos
  have hH : (0 : ℝ) ≤ (H m (upperEndpoint m) (mixedCount m upper) : ℝ) := by
    rw [H_cast]
    exact h.H_pos.le
  exact ⟨by exact_mod_cast hj, by exact_mod_cast hH, (endpoint_defect m).1, (endpoint_defect m).2⟩

/-- The parent generator count is exactly the required child/mixed/pure sum. -/
theorem parent_count_identity (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    parentCount m upper = upperEndpoint m+mixedCount m upper+4 := by
  have h := parent_ge_child_add_six m hm upper
  unfold mixedCount
  omega

/-- The actual integer source dimension agrees with the real polynomial `3m-c`. -/
theorem source_dimension_cast (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    (ProfileCertificate.totalA m (mixedCount m upper) : ℝ) = aR m (mixedCount m upper) := by
  have hc := c_range m hm upper
  rw [ProfileCertificate.totalA_eq m (mixedCount m upper) hc.1 hc.2]
  rw [Nat.cast_sub (by omega : mixedCount m upper ≤ 3*m)]
  push_cast
  rfl

/-- Actual source dimension, ratio, and domination conditions for the scalar argument. -/
theorem actual_domination (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    let c := mixedCount m upper
    let a : ℝ := ProfileCertificate.totalA m c
    let J : ℝ := j m (upperEndpoint m) c
    0 < a ∧ 0 ≤ J/a ∧ J/a ≤ 2*(m : ℝ)/3+1 ∧
      (c : ℝ)+4+a-J/a < (m : ℝ)^2/100 ∧
      a+J/a < (m : ℝ)^2/100 ∧ a < (m : ℝ)^2/100 := by
  have h := actual_validCounts m hm upper
  dsimp
  rw [source_dimension_cast m hm upper, j_cast]
  exact ⟨h.a_bounds.1, h.j_div_a.1, h.j_div_a.2, h.domination.1, h.domination.2.1, h.domination.2.2⟩

/-- Cubic target Euler dimension before imposing the child quadrics. -/
def targetCount (m c : ℕ) : ℤ := 3*b3 m-(c : ℤ)*b2 m

/-- The source/target Euler relation in real notation. -/
theorem target_count_identity (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    (targetCount m (mixedCount m upper) : ℝ) =
      (upperEndpoint m : ℝ)*(ProfileCertificate.totalA m (mixedCount m upper) : ℝ) +
        (j m (upperEndpoint m) (mixedCount m upper) : ℝ) := by
  rw [source_dimension_cast m hm upper, j_cast]
  simp only [targetCount, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, b2_cast, b3_cast]
  unfold jR betaR alphaR aR
  ring

/-- The same target count equals the proved free-extension Hilbert expression. -/
theorem target_count_eq_free (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    let c := mixedCount m upper
    let w := ProfileCertificate.freeW m c
    targetCount m c = ProfileCertificate.coreB c*(w : ℤ) +
      (ProfileCertificate.coreA c : ℤ)*b2 w + 3*b3 w := by
  have hc := c_range m hm upper
  have hw : (ProfileCertificate.freeW m (mixedCount m upper) : ℝ) =
      (m : ℝ)-(mixedCount m upper : ℝ)+2 := by
    unfold ProfileCertificate.freeW
    rw [Nat.cast_add, Nat.cast_sub hc.2]
    norm_num
  have hp : (ProfileCertificate.coreP (mixedCount m upper) : ℝ) =
      (mixedCount m upper : ℝ)-3 := by
    unfold ProfileCertificate.coreP
    rw [Nat.cast_sub (by omega : 3 ≤ mixedCount m upper)]
    norm_num
  have hA : (ProfileCertificate.coreA (mixedCount m upper) : ℝ) =
      2*((mixedCount m upper : ℝ)-3) := by
    simp only [ProfileCertificate.coreA, Nat.cast_mul, Nat.cast_ofNat, hp]
  have hB : (ProfileCertificate.coreB (mixedCount m upper) : ℝ) =
      ((mixedCount m upper : ℝ)-3)*((mixedCount m upper : ℝ)-2)/2 := by
    simp only [ProfileCertificate.coreB, FiniteCounts.quadratics_eq_b2, b2_cast, hp]
    ring
  have heq : (targetCount m (mixedCount m upper) : ℝ) =
      (ProfileCertificate.coreB (mixedCount m upper) : ℝ)*(ProfileCertificate.freeW m (mixedCount m upper) : ℝ) +
      (ProfileCertificate.coreA (mixedCount m upper) : ℝ)*(b2 (ProfileCertificate.freeW m (mixedCount m upper)) : ℝ) +
      3*(b3 (ProfileCertificate.freeW m (mixedCount m upper)) : ℝ) := by
    simp only [targetCount, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, b2_cast, b3_cast]
    rw [hA, hB, hw]
    ring
  exact_mod_cast heq

end
end Quartic.UniformScalar
