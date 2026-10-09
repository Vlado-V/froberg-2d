module

public import Quartic.FiniteCounts
public import Quartic.UniformCertificate

@[expose] public section

/-!
# Actual endpoint parameters in the uniform Bernstein rectangle

The endpoints in this file are defined for every natural number by the Euler
sign condition, independently of the finite table. The resulting theorem
instantiates the uniform vertex inequalities at actual transfer counts. It
does not assert the geometric concavity or scalar incidence bridges.
-/

namespace Quartic.UniformEndpoint

open Quartic.Counts

/-- A nonpositive Euler count always exists in the allowed generator range. -/
theorem endpoint_exists (n : ℕ) : ∃ r : ℕ, chi n r ≤ 0 :=
  ⟨(n + 1).choose 2, full_quadratic_count_chi_nonpos n⟩

/-- The actual upper endpoint, valid in every dimension. -/
def upperEndpoint (n : ℕ) : ℕ := Nat.find (endpoint_exists n)

/-- The adjacent lower endpoint, including the integral-root case. -/
def lowerEndpoint (n : ℕ) : ℕ :=
  if chi n (upperEndpoint n) = 0 then upperEndpoint n else upperEndpoint n - 1

theorem upper_nonpositive (n : ℕ) : chi n (upperEndpoint n) ≤ 0 :=
  Nat.find_spec (endpoint_exists n)

theorem before_upper_positive (n r : ℕ) (hr : r < upperEndpoint n) : 0 < chi n r := by
  have h := Nat.find_min (endpoint_exists n) hr
  omega

theorem upper_le_quadratics (n : ℕ) : upperEndpoint n ≤ (n + 1).choose 2 :=
  Nat.find_min' (endpoint_exists n) (full_quadratic_count_chi_nonpos n)

theorem lower_upper_adjacent (n : ℕ) :
    lowerEndpoint n ≤ upperEndpoint n ∧ upperEndpoint n ≤ lowerEndpoint n + 1 := by
  unfold lowerEndpoint
  split_ifs <;> omega

/-- The real Euler polynomial agrees with the original integer binomial count. -/
noncomputable def eulerReal (n r : ℝ) : ℝ :=
  n * (n + 1) * (n + 2) * (n + 3) / 24 - r * n * (n + 1) / 2 + r * (r - 1) / 2

theorem chi_cast (n r : ℕ) : (chi n r : ℝ) = eulerReal n r := by
  have h₂ : 2 * (b2 n : ℝ) = (n : ℝ) * ((n : ℝ) + 1) := by exact_mod_cast b2_scaled n
  have h₄ : 24 * (b4 n : ℝ) = (n : ℝ) * ((n : ℝ) + 1) *
      ((n : ℝ) + 2) * ((n : ℝ) + 3) := by exact_mod_cast b4_scaled n
  have hr : 2 * (r.choose 2 : ℝ) = (r : ℝ) * ((r : ℝ) - 1) := by
    exact_mod_cast choose_two_scaled r
  simp only [chi, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast, eulerReal]
  linear_combination (1 / 24 : ℝ) * h₄ - ((r : ℝ) / 2) * h₂ + (1 / 2 : ℝ) * hr

/-- The Euler polynomial decreases throughout the possible generator range. -/
theorem eulerReal_antitone (n r s : ℝ) (hrs : r ≤ s) (hs : s ≤ n * (n + 1) / 2) :
    eulerReal n s ≤ eulerReal n r := by
  have hfactor : s + r - n * (n + 1) - 1 ≤ 0 := by nlinarith
  have hprod := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hrs) hfactor
  have hid : 2 * (eulerReal n s - eulerReal n r) =
      (s - r) * (s + r - n * (n + 1) - 1) := by unfold eulerReal; ring
  nlinarith only [hprod, hid]

noncomputable def rho : ℝ := (3 - Real.sqrt 6) / 6

theorem rho_bounds : (11 : ℝ) / 120 ≤ rho ∧ rho ≤ 7 / 75 := by
  have hs0 := Real.sqrt_nonneg (6 : ℝ)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  unfold rho
  constructor <;> nlinarith

theorem rho_identity : 12 * rho^2 - 12 * rho + 1 = 0 := by
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  unfold rho
  nlinarith only [hs2]

noncomputable def baseCount (n : ℝ) : ℝ := rho * n^2 + n / 2

theorem eulerReal_base (n : ℝ) :
    eulerReal n (baseCount n) = (1 / 3 - rho / 2) * n^2 := by
  unfold eulerReal baseCount
  linear_combination (n^4 / 24) * rho_identity

theorem eulerReal_base_add_one (n : ℝ) :
    eulerReal n (baseCount n + 1) = (rho / 2 - 1 / 6) * n^2 := by
  unfold eulerReal baseCount
  linear_combination (n^4 / 24) * rho_identity

theorem base_le_quadratic (n : ℝ) : baseCount n ≤ n * (n + 1) / 2 := by
  have hr := rho_bounds.2
  have hp : 0 ≤ (1 / 2 - rho) * n^2 := mul_nonneg (by linarith) (sq_nonneg n)
  unfold baseCount
  nlinarith only [hp]

/-- Elementary algebra locates the actual upper endpoint within two of the
quadratic approximation. No asymptotic estimate or derivative is assumed. -/
theorem upper_endpoint_bounds (n : ℕ) (hn : 0 < n) :
    baseCount n ≤ (upperEndpoint n : ℝ) ∧ (upperEndpoint n : ℝ) ≤ baseCount n + 2 := by
  have hnq : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := rho_bounds
  have hbpos : 0 < baseCount (n : ℝ) := by
    unfold baseCount
    have hrpos : (0 : ℝ) < rho := by linarith
    positivity
  have hbasepos : 0 < eulerReal n (baseCount n) := by
    rw [eulerReal_base]
    exact mul_pos (by linarith [hr.2]) (sq_pos_of_pos hnq)
  have hbaseneg : eulerReal n (baseCount n + 1) < 0 := by
    rw [eulerReal_base_add_one]
    exact mul_neg_of_neg_of_pos (by linarith [hr.2]) (sq_pos_of_pos hnq)
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
    have hlt : (upperEndpoint n : ℝ) < baseCount n := by linarith
    have hmono := eulerReal_antitone n (upperEndpoint n) (baseCount n) hlt.le (base_le_quadratic n)
    linarith
  · by_contra h
    have hlt : baseCount n + 2 < (upperEndpoint n : ℝ) := by linarith
    have hqpos : 0 < upperEndpoint n := by
      have hq : (0 : ℝ) < upperEndpoint n := by linarith
      exact_mod_cast hq
    have hpred : ((upperEndpoint n - 1 : ℕ) : ℝ) = (upperEndpoint n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ upperEndpoint n), Nat.cast_one]
    have hp : 0 < eulerReal n ((upperEndpoint n - 1 : ℕ) : ℝ) := by
      rw [← chi_cast]
      exact_mod_cast before_upper_positive n (upperEndpoint n - 1) (by omega)
    have hmono := eulerReal_antitone n (baseCount n + 1) ((upperEndpoint n - 1 : ℕ) : ℝ)
      (by rw [hpred]; linarith) (by rw [hpred]; linarith)
    linarith

/-- Either adjacent endpoint in the parent dimension. -/
def parentCount (m : ℕ) (upper : Bool) : ℕ :=
  if upper then upperEndpoint (m + 3) else lowerEndpoint (m + 3)

def mixedCount (m : ℕ) (upper : Bool) : ℕ := parentCount m upper - upperEndpoint m - 4

/-- The core variable count `t = c - 2`, before normalization. -/
def coreVariables (m : ℕ) (upper : Bool) : ℕ := parentCount m upper - upperEndpoint m - 6

theorem coreVariables_eq_mixed_sub_two (m : ℕ) (upper : Bool) :
    coreVariables m upper = mixedCount m upper - 2 := by
  unfold coreVariables mixedCount
  omega

theorem parent_endpoint_bounds (m : ℕ) (upper : Bool) :
    baseCount (m + 3 : ℕ) - 1 ≤ (parentCount m upper : ℝ) ∧
    (parentCount m upper : ℝ) ≤ baseCount (m + 3 : ℕ) + 2 := by
  have hq := upper_endpoint_bounds (m + 3) (by omega)
  have hadj := lower_upper_adjacent (m + 3)
  have hlo : (lowerEndpoint (m + 3) : ℝ) ≤ (upperEndpoint (m + 3) : ℝ) := by
    exact_mod_cast hadj.1
  have hhi : (upperEndpoint (m + 3) : ℝ) ≤ (lowerEndpoint (m + 3) : ℝ) + 1 := by
    exact_mod_cast hadj.2
  cases upper <;> simp only [parentCount, Bool.false_eq_true, ite_false, ite_true] <;>
    constructor <;> linarith

/-- Coarse endpoint bounds already put the exact raw core count in the needed interval. -/
theorem raw_core_bounds (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    (m : ℝ) / 2 ≤ (parentCount m upper : ℝ) - (upperEndpoint m : ℝ) - 6 ∧
    (parentCount m upper : ℝ) - (upperEndpoint m : ℝ) - 6 ≤ (14 / 25 : ℝ) * (m : ℝ) := by
  have hq := upper_endpoint_bounds m (by omega)
  have hp := parent_endpoint_bounds m upper
  have hdiff : baseCount (m + 3 : ℕ) - baseCount m =
      6 * rho * (m : ℝ) + 9 * rho + 3 / 2 := by
    unfold baseCount
    push_cast
    ring
  have hmR : (320 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hr := rho_bounds
  have hlow := mul_nonneg (sub_nonneg.mpr hr.1) hm0
  have hupp := mul_nonneg (sub_nonneg.mpr hr.2) hm0
  constructor <;> nlinarith

theorem parent_ge_child_add_six (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    upperEndpoint m + 6 ≤ parentCount m upper := by
  have h := (raw_core_bounds m hm upper).1
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hc : (upperEndpoint m : ℝ) + 6 ≤ (parentCount m upper : ℝ) := by linarith
  exact_mod_cast hc

theorem coreVariables_cast (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    (coreVariables m upper : ℝ) = (parentCount m upper : ℝ) - (upperEndpoint m : ℝ) - 6 := by
  have h := parent_ge_child_add_six m hm upper
  unfold coreVariables
  rw [Nat.cast_sub (by omega : 6 ≤ parentCount m upper - upperEndpoint m),
    Nat.cast_sub (by omega : upperEndpoint m ≤ parentCount m upper)]
  norm_num

/-- The actual endpoint core count lies between `m/2` and `14m/25` for all `m≥320`. -/
theorem core_count_bounds (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    (m : ℝ) / 2 ≤ (coreVariables m upper : ℝ) ∧
      (coreVariables m upper : ℝ) ≤ (14 / 25 : ℝ) * (m : ℝ) := by
  rw [coreVariables_cast m hm upper]
  exact raw_core_bounds m hm upper

noncomputable def normalizedZ (m : ℕ) (upper : Bool) : ℝ := (coreVariables m upper : ℝ) / (m : ℝ)
noncomputable def normalizedU (m : ℕ) : ℝ := 1 / (m : ℝ)

/-- Actual transfer endpoint parameters lie in the full certified rectangle. -/
theorem endpoint_rectangle (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    1 / 2 ≤ normalizedZ m upper ∧ normalizedZ m upper ≤ 14 / 25 ∧
      0 ≤ normalizedU m ∧ normalizedU m ≤ 1 / 64 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmR : (320 : ℝ) ≤ m := by exact_mod_cast hm
  have ht := core_count_bounds m hm upper
  unfold normalizedZ normalizedU
  refine ⟨(le_div_iff₀ hmpos).2 (by linarith [ht.1]),
    (div_le_iff₀ hmpos).2 ht.2, by positivity, ?_⟩
  apply (div_le_iff₀ hmpos).2
  linarith

/-- All 32 uniform Bernstein vertex inequalities at the actual transfer endpoint
parameters, with no upper bound on the child dimension. -/
theorem actual_endpoint_bernstein (m : ℕ) (hm : 320 ≤ m) (upper : Bool)
    (cell r : Fin 4) (side : Fin 2) :
    0 ≤ UniformCertificate.inequalityPolynomial cell r side (normalizedZ m upper) (normalizedU m) := by
  have h := endpoint_rectangle m hm upper
  exact UniformCertificate.uniform_bernstein_inequality cell r side _ _
    h.1 h.2.1 h.2.2.1 h.2.2.2

/-- The all-dimension upper endpoint agrees with every certified finite record. -/
theorem upperEndpoint_eq_table (n : ℕ) (hn : n ≤ 322) :
    upperEndpoint n = FiniteCounts.upperEndpoint n := by
  have ht := FiniteCounts.endpoint_table_verified ⟨n, by omega⟩
  change FiniteCounts.EndpointValid n (FiniteCounts.lowerEndpoint n) (FiniteCounts.upperEndpoint n) at ht
  rcases ht with ⟨hlu, hadj, hquad, hlo, hup, hroot, hstrict⟩
  simp only [FiniteCounts.euler_eq_chi] at hlo hup hroot hstrict
  have hule : FiniteCounts.upperEndpoint n ≤ (n + 1).choose 2 := by
    rw [FiniteCounts.quadratics_eq_b2] at hquad
    unfold b2 at hquad
    exact_mod_cast hquad
  have hle : upperEndpoint n ≤ FiniteCounts.upperEndpoint n := Nat.find_min' (endpoint_exists n) hup
  apply le_antisymm hle
  by_contra h
  have hlt : upperEndpoint n < FiniteCounts.upperEndpoint n := by omega
  have hq := upper_nonpositive n
  by_cases heq : FiniteCounts.lowerEndpoint n = FiniteCounts.upperEndpoint n
  · have hz : chi n (FiniteCounts.upperEndpoint n) = 0 := by
      rw [← heq]
      exact hroot.mp heq
    have hdec := chi_strictAntiOn n (upper_le_quadratics n) hule hlt
    omega
  · have hlu' : FiniteCounts.lowerEndpoint n < FiniteCounts.upperEndpoint n := by omega
    have hpos := (hstrict hlu').2
    have hql : upperEndpoint n ≤ FiniteCounts.lowerEndpoint n := by omega
    rcases lt_or_eq_of_le hql with hsmall | hequal
    · have hdec := chi_strictAntiOn n (upper_le_quadratics n) (le_trans hlu hule) hsmall
      omega
    · rw [hequal] at hq
      omega

/-- The all-dimension lower endpoint also agrees with every finite record. -/
theorem lowerEndpoint_eq_table (n : ℕ) (hn : n ≤ 322) :
    lowerEndpoint n = FiniteCounts.lowerEndpoint n := by
  have ht := FiniteCounts.endpoint_table_verified ⟨n, by omega⟩
  change FiniteCounts.EndpointValid n (FiniteCounts.lowerEndpoint n) (FiniteCounts.upperEndpoint n) at ht
  rcases ht with ⟨hlu, hadj, _, _, _, hroot, hstrict⟩
  simp only [FiniteCounts.euler_eq_chi] at hroot hstrict
  unfold lowerEndpoint
  rw [upperEndpoint_eq_table n hn]
  by_cases heq : FiniteCounts.lowerEndpoint n = FiniteCounts.upperEndpoint n
  · have hz : chi n (FiniteCounts.upperEndpoint n) = 0 := by
      rw [← heq]
      exact hroot.mp heq
    simp only [hz, ite_true]
    omega
  · have hlt : FiniteCounts.lowerEndpoint n < FiniteCounts.upperEndpoint n := by omega
    have hz : chi n (FiniteCounts.upperEndpoint n) ≠ 0 := ne_of_lt (hstrict hlt).1
    simp only [hz, ite_false]
    omega

/-- The finite and all-dimension transfer generator counts are identical on their overlap. -/
theorem mixedCount_eq_table (m : ℕ) (hm : m ≤ 319) (upper : Bool) :
    mixedCount m upper = FiniteCounts.mixedCount m upper := by
  unfold mixedCount parentCount FiniteCounts.mixedCount FiniteCounts.parentCount
  rw [upperEndpoint_eq_table m (by omega),
    upperEndpoint_eq_table (m + 3) (by omega), lowerEndpoint_eq_table (m + 3) (by omega)]

end Quartic.UniformEndpoint
