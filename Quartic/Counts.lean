module

public import Mathlib

@[expose] public section

/-!
# Integer dimension counts for quartic multiplication

These are arithmetic statements only. They do not assume generic maximal rank.
The counts use natural binomial coefficients, cast to integers so that Euler
characteristics and endpoint defects are allowed to be negative.
-/

namespace Quartic.Counts

/-- Number of quadratic monomials in `n` variables. -/
def b2 (n : ℕ) : ℤ := Nat.choose (n + 1) 2

/-- Number of cubic monomials in `n` variables. -/
def b3 (n : ℕ) : ℤ := Nat.choose (n + 2) 3

/-- Number of quartic monomials in `n` variables. -/
def b4 (n : ℕ) : ℤ := Nat.choose (n + 3) 4

/-- Euler difference after accounting for the quadratic Koszul relations. -/
def chi (n r : ℕ) : ℤ := b4 n - (r : ℤ) * b2 n + Nat.choose r 2

/-- The exact first difference of the Euler polynomial. -/
theorem chi_succ_sub (n r : ℕ) :
    chi n (r + 1) - chi n r = (r : ℤ) - b2 n := by
  simp only [chi, Nat.choose_succ_succ', Nat.choose_one_right,
    Nat.cast_add, Nat.cast_one]
  ring

/-- The Euler difference decreases at every count below the quadratic dimension. -/
theorem chi_succ_lt (n r : ℕ) (hr : r < Nat.choose (n + 1) 2) :
    chi n (r + 1) < chi n r := by
  have h : (r : ℤ) < b2 n := by
    unfold b2
    exact_mod_cast hr
  have := chi_succ_sub n r
  omega

/-- Strict decrease on the interval of possible dimensions of a quadratic subspace. -/
theorem chi_strictAntiOn (n : ℕ) :
    StrictAntiOn (chi n) (Set.Iic (Nat.choose (n + 1) 2)) := by
  apply strictAntiOn_Iic_of_succ_lt
  intro r hr
  exact chi_succ_lt n r hr

/-- A nonintegral adjacent endpoint has defect at most the remaining quadratic dimension. -/
theorem endpoint_defect_bounds (n r : ℕ)
    (hprev : 0 < chi n r) (hnext : chi n (r + 1) ≤ 0) :
    0 ≤ -chi n (r + 1) ∧
      -chi n (r + 1) ≤ b2 n - ((r + 1 : ℕ) : ℤ) := by
  have h := chi_succ_sub n r
  simp only [Nat.cast_add, Nat.cast_one]
  omega

/-- The same defect bound includes the case where the endpoint is an exact root. -/
theorem endpoint_defect_bounds_or_root (n q : ℕ)
    (hq : (q : ℤ) ≤ b2 n) (hnonpos : chi n q ≤ 0)
    (hboundary : chi n q = 0 ∨ ∃ r, q = r + 1 ∧ 0 < chi n r) :
    0 ≤ -chi n q ∧ -chi n q ≤ b2 n - (q : ℤ) := by
  rcases hboundary with hzero | ⟨r, rfl, hprev⟩
  · simp only [hzero, neg_zero]
    omega
  · exact endpoint_defect_bounds n r hprev hnonpos

/-- Integer form of the quadratic monomial count. -/
theorem b2_scaled (n : ℕ) : 2 * b2 n = (n : ℤ) * ((n : ℤ) + 1) := by
  have h := congrArg Int.ofNat (Nat.add_one_mul_choose_eq n 1)
  simp only [Nat.choose_one_right] at h
  change ((n : ℤ) + 1) * (n : ℤ) = b2 n * 2 at h
  nlinarith

/-- Integer form of the cubic monomial count. -/
theorem b3_scaled (n : ℕ) :
    6 * b3 n = (n : ℤ) * ((n : ℤ) + 1) * ((n : ℤ) + 2) := by
  have h := congrArg Int.ofNat (Nat.add_one_mul_choose_eq (n + 1) 2)
  change (((n : ℤ) + 1) + 1) * b2 n = b3 n * 3 at h
  linear_combination -2 * h + ((n : ℤ) + 2) * b2_scaled n

/-- Integer form of the quartic monomial count. -/
theorem b4_scaled (n : ℕ) :
    24 * b4 n = (n : ℤ) * ((n : ℤ) + 1) * ((n : ℤ) + 2) * ((n : ℤ) + 3) := by
  have h := congrArg Int.ofNat (Nat.add_one_mul_choose_eq (n + 2) 3)
  change (((n : ℤ) + 2) + 1) * b3 n = b4 n * 4 at h
  linear_combination -6 * h + ((n : ℤ) + 3) * b3_scaled n

/-- Integer binomial identity valid even at `r = 0`. -/
theorem choose_two_scaled (r : ℕ) :
    2 * (Nat.choose r 2 : ℤ) = (r : ℤ) * ((r : ℤ) - 1) := by
  cases r with
  | zero => norm_num
  | succ r =>
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right, mul_comm, b2] using b2_scaled r

/-- Remaining quadratic dimension at the child generator count. -/
def alpha (m q : ℕ) : ℤ := b2 m - (q : ℤ)

/-- Cubic Euler difference at the child generator count. -/
def beta (m q : ℕ) : ℤ := b3 m - (m : ℤ) * (q : ℤ)

/-- Middle homology count from the transfer construction. -/
def H (m q c : ℕ) : ℤ :=
  3 * (m : ℤ) * (c : ℤ) - 2 * alpha m q - Nat.choose c 2

/-- The count for the `(3,1)` block. -/
def k31 (m c : ℕ) : ℤ := 2 * (m : ℤ) + 2 * (c : ℤ)

/-- The outer cokernel Euler difference. -/
def j (m q c : ℕ) : ℤ := 3 * beta m q - (c : ℤ) * alpha m q

/-- Child endpoint defect, without any sign assumption. -/
def delta (m q : ℕ) : ℤ := -chi m q

/-- Sum of the three homology counts in the transfer. -/
def hTotal (m q c : ℕ) : ℤ := H m q c + k31 m c + 3 + delta m q

/-- The transfer dimensions reproduce the parent Euler difference exactly.

The parent generator count is written as `q + c + 4`, so this theorem requires
no convention about truncated natural subtraction in the definition of `c`.
-/
theorem transfer_euler_identity (m q c : ℕ) :
    j m q c - hTotal m q c = chi (m + 3) (q + c + 4) := by
  have hb2 := b2_scaled m
  have hb3 := b3_scaled m
  have hb4 := b4_scaled m
  have hp2 := b2_scaled (m + 3)
  have hp4 := b4_scaled (m + 3)
  have hq := choose_two_scaled q
  have hc := choose_two_scaled c
  have hr := choose_two_scaled (q + c + 4)
  push_cast at hp2 hp4 hr
  have h : 24 * (j m q c - hTotal m q c - chi (m + 3) (q + c + 4)) = 0 := by
    unfold j hTotal H k31 delta beta alpha chi
    push_cast
    linear_combination hb4 + 12 * hb3 +
      (24 - 12 * (q : ℤ) - 12 * (c : ℤ)) * hb2 - hp4 +
      (12 * (q : ℤ) + 12 * (c : ℤ) + 48) * hp2 +
      12 * hq + 12 * hc - 12 * hr
  omega

/-- At the full quadratic dimension, the Euler polynomial has a simple negative
factorization. This identity also covers zero and one variable. -/
theorem full_quadratic_count_chi_scaled (n : ℕ) :
    12 * chi n (Nat.choose (n + 1) 2) =
      -(n : ℤ) ^ 2 * ((n : ℤ) - 1) * ((n : ℤ) + 1) := by
  have hb2 := b2_scaled n
  have hb4 := b4_scaled n
  have hc := choose_two_scaled (Nat.choose (n + 1) 2)
  change 2 * (Nat.choose (Nat.choose (n + 1) 2) 2 : ℤ) =
    b2 n * (b2 n - 1) at hc
  have h : 24 * chi n (Nat.choose (n + 1) 2) =
      -2 * (n : ℤ) ^ 2 * ((n : ℤ) - 1) * ((n : ℤ) + 1) := by
    unfold chi
    change 24 * (b4 n - b2 n * b2 n +
      (Nat.choose (Nat.choose (n + 1) 2) 2 : ℤ)) = _
    linear_combination hb4 + 12 * hc -
      (6 * b2 n + 3 * (n : ℤ) * ((n : ℤ) + 1) + 6) * hb2
  nlinarith

/-- The Euler difference is nonpositive at the full space of quadrics. -/
theorem full_quadratic_count_chi_nonpos (n : ℕ) :
    chi n (Nat.choose (n + 1) 2) ≤ 0 := by
  have h := full_quadratic_count_chi_scaled n
  by_cases hn : n = 0
  · subst n
    norm_num at h ⊢
    omega
  · have hn1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hprod : 0 ≤ (n : ℤ) ^ 2 * ((n : ℤ) - 1) * ((n : ℤ) + 1) := by
      apply mul_nonneg
      · exact mul_nonneg (sq_nonneg _) (by omega)
      · omega
    nlinarith

end Quartic.Counts
