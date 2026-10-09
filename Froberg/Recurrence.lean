module

public import Mathlib

@[expose] public section

/-!
# The numerical recurrence argument for the two endpoint defects

This file proves the discrete implications used in Sections 6 and 7 of the
manuscript.  The hypotheses about transfer, divisibility, and the existence of
zeros are explicit: this file does not establish those geometric or
equidistribution inputs for generic polynomial ideals.
-/

namespace Froberg

/-- Transfer estimates with the two opposite Euler-characteristic signs bound
both new defects by any common bound for the retained child defects. -/
theorem transfer_defects_le
    (a b k c M : ℕ) (x y : ℤ)
    (hx : 0 ≤ x) (hy : y ≤ 0)
    (ha : (a : ℤ) ≤ max (k : ℤ) ((c : ℤ) - x))
    (hb : (b : ℤ) ≤ max (c : ℤ) ((k : ℤ) + y))
    (hk : k ≤ M) (hc : c ≤ M) :
    max a b ≤ M := by
  have hax : max (k : ℤ) ((c : ℤ) - x) ≤ (M : ℤ) := by
    apply max_le <;> omega
  have hby : max (c : ℤ) ((k : ℤ) + y) ≤ (M : ℤ) := by
    apply max_le <;> omega
  apply max_le <;> omega

/-- In particular, taking the old defect to be the maximum of the two child
defects gives the asserted recurrence bound. -/
theorem transfer_implies_recurrence
    (a b k c H C : ℕ) (x y : ℤ)
    (hx : 0 ≤ x) (hy : y ≤ 0)
    (ha : (a : ℤ) ≤ max (k : ℤ) ((c : ℤ) - x))
    (hb : (b : ℤ) ≤ max (c : ℤ) ((k : ℤ) + y))
    (hk : k ≤ H) (hc : c ≤ C) :
    max a b ≤ max H C :=
  transfer_defects_le a b k c (max H C) x y hx hy ha hb
    (hk.trans (le_max_left _ _)) (hc.trans (le_max_right _ _))

/-- Iterate a recurrence without requiring an initial zero. -/
theorem recurrence_iterate
    (E : ℕ → ℕ) (h start : ℕ)
    (hstep : ∀ n, start ≤ n → E (n + h) ≤ E n)
    (n : ℕ) (hn : start ≤ n) (t : ℕ) :
    E (n + t * h) ≤ E n := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.succ_mul, ← Nat.add_assoc]
      exact (hstep (n + t * h) (by omega)).trans ih

/-- A bound on one initial window propagates to every later index. -/
theorem recurrence_bound_from_window
    (E : ℕ → ℕ) (h start M : ℕ) (hh : 0 < h)
    (hstep : ∀ n, start ≤ n → E (n + h) ≤ E n)
    (hwindow : ∀ n, start ≤ n → n < start + h → E n ≤ M) :
    ∀ n, start ≤ n → E n ≤ M := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      by_cases hlt : n < start + h
      · exact hwindow n hn hlt
      · have hbase : start ≤ n - h := by omega
        have hsmaller : n - h < n := by omega
        have heq : n - h + h = n := by omega
        have hrec := hstep (n - h) hbase
        rw [heq] at hrec
        exact hrec.trans (ih (n - h) hsmaller hbase)

/-- Every eventually nonincreasing fixed-step natural-number sequence is
bounded on the tail where the recurrence holds. -/
theorem recurrence_eventually_bounded
    (E : ℕ → ℕ) (h start : ℕ) (hh : 0 < h)
    (hstep : ∀ n, start ≤ n → E (n + h) ≤ E n) :
    ∃ M : ℕ, ∀ n, start ≤ n → E n ≤ M := by
  refine ⟨(Finset.range (start + h)).sup E, ?_⟩
  apply recurrence_bound_from_window E h start _ hh hstep
  intro n _ hn
  exact Finset.le_sup (f := E) (Finset.mem_range.mpr hn)

/-- A zero propagates along its residue class. -/
theorem recurrence_zero_propagates
    (E : ℕ → ℕ) (h start : ℕ)
    (hstep : ∀ n, start ≤ n → E (n + h) ≤ E n)
    (n : ℕ) (hn : start ≤ n) (hzero : E n = 0) (t : ℕ) :
    E (n + t * h) = 0 := by
  have hle := recurrence_iterate E h start hstep n hn t
  rw [hzero] at hle
  exact Nat.eq_zero_of_le_zero hle

/-- A zero in each residue class, after the recurrence begins, suffices for
eventual vanishing.  This is the final finite-residue step of the argument. -/
theorem eventual_zero_of_recurrence_and_residue_zeros
    (E : ℕ → ℕ) (h start : ℕ) (hh : 0 < h)
    (hstep : ∀ n, start ≤ n → E (n + h) ≤ E n)
    (hzeros : ∀ b : Fin h, ∃ n : ℕ,
      start ≤ n ∧ n % h = b.val ∧ E n = 0) :
    ∃ N : ℕ, ∀ n, N ≤ n → E n = 0 := by
  classical
  choose w hwstart hwmod hwzero using hzeros
  refine ⟨Finset.univ.sup w, ?_⟩
  intro n hn
  let b : Fin h := ⟨n % h, Nat.mod_lt n hh⟩
  have hwb : w b ≤ n :=
    (Finset.le_sup (f := w) (Finset.mem_univ b)).trans hn
  have hcong : Nat.ModEq h (w b) n := hwmod b
  obtain ⟨t, ht⟩ := hcong.dvd'
  have heq : w b + t * h = n := by
    rw [Nat.mul_comm t h]
    omega
  rw [← heq]
  exact recurrence_zero_propagates E h start hstep (w b)
    (hwstart b) (hwzero b) t

/-- The arbitrarily-late-zero version used after the arithmetic selection of
critical counts. -/
theorem eventual_zero_of_recurrence_and_late_residue_zeros
    (E : ℕ → ℕ) (h start : ℕ) (hh : 0 < h)
    (hstep : ∀ n, start ≤ n → E (n + h) ≤ E n)
    (hzeros : ∀ b : Fin h, ∀ B : ℕ, ∃ n : ℕ,
      B ≤ n ∧ n % h = b.val ∧ E n = 0) :
    ∃ N : ℕ, ∀ n, N ≤ n → E n = 0 :=
  eventual_zero_of_recurrence_and_residue_zeros E h start hh hstep
    (fun b => hzeros b start)

/-- A natural number below a positive divisor is zero if that divisor divides
it.  No primality hypothesis is necessary. -/
theorem zero_of_dvd_and_bound
    (a M p : ℕ) (ha : a ≤ M) (hp : M < p) (hdiv : p ∣ a) :
    a = 0 := by
  by_contra hne
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdiv
  omega

/-- The manuscript chooses primes larger than the *scaled* defect bound.
That stronger inequality forces vanishing directly, before cancelling the
factor `c` from the divisibility statement. -/
theorem zero_of_scaled_dvd_and_bound
    (a M p c : ℕ) (hc : 0 < c) (ha : a ≤ M)
    (hp : c * M < p) (hdiv : p ∣ c * a) :
    a = 0 := by
  have hzero : c * a = 0 :=
    zero_of_dvd_and_bound (c * a) (c * M) p
      (Nat.mul_le_mul_left c ha) hp hdiv
  exact (Nat.mul_eq_zero.mp hzero).resolve_left (Nat.ne_of_gt hc)

/-- Apply the scaled divisibility argument to both endpoint defects. -/
theorem two_defects_zero_of_scaled_divisibility
    (a b M p q c : ℕ) (hc : 0 < c)
    (ha : a ≤ M) (hb : b ≤ M)
    (hp : c * M < p) (hq : c * M < q)
    (hpa : p ∣ c * a) (hqb : q ∣ c * b) :
    max a b = 0 := by
  rw [zero_of_scaled_dvd_and_bound a M p c hc ha hp hpa,
    zero_of_scaled_dvd_and_bound b M q c hc hb hq hqb]
  rfl

end Froberg
