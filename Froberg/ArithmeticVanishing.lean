import Froberg.Recurrence
import Froberg.PolynomialHits

/-!
# Eventual vanishing from the numerical arithmetic inputs

This file proves the abstract arithmetic implication in Theorem 7.4.  Its
inputs are the recurrence, the actual gcd divisibility statements, and the
polynomial approximation to the critical root.  Establishing those inputs
for the generic polynomial multiplication maps is separate mathematical work.

The proof uses large composite coprime moduli instead of primes.  Their
explicit construction and the stronger bound on the scaled defects remove
the need for prime existence or cancellation of the factor `2 * d`.
-/

namespace Froberg

open Polynomial
open scoped Topology

/-- Explicit arbitrarily large coprime moduli, each coprime to the recurrence
step.  One can take `p = h * (B + 1) + 1` and `q = h * p + 1`. -/
theorem exists_large_coprime_moduli
    (h B : ℕ) (hh : 0 < h) :
    ∃ p q : ℕ, B < p ∧ B < q ∧ Nat.Coprime p q ∧ Nat.Coprime h (p * q) := by
  let p := h * (B + 1) + 1
  let q := h * p + 1
  have hp : B < p := by dsimp only [p]; nlinarith
  have hq : B < q := by dsimp only [q]; nlinarith
  have hpq : Nat.Coprime p q := by
    dsimp only [q]
    rw [Nat.coprime_mul_right_add_right]
    exact Nat.coprime_one_right p
  have hhp : Nat.Coprime h p := by
    dsimp only [p]
    rw [Nat.coprime_mul_left_add_right]
    exact Nat.coprime_one_right h
  have hhq : Nat.Coprime h q := by
    dsimp only [q]
    rw [Nat.coprime_mul_left_add_right]
    exact Nat.coprime_one_right h
  exact ⟨p, q, hp, hq, hpq, hhp.mul_right hhq⟩

/-- The complete abstract arithmetic vanishing theorem.

`H n` and `C n` are the two critical defects; their generator counts are the
natural floor and ceiling of `κ n`.  If their maximum satisfies a fixed-step
recurrence, the gcd divisibilities hold on that tail, and `κ` is asymptotic
to an irrational-leading polynomial up to an error tending to zero, then
both defects vanish eventually.
-/
theorem arithmetic_eventual_vanishing
    (d h start : ℕ) (hd : 0 < d) (hh : 0 < h)
    (P : Polynomial ℝ) (hP : 0 < P.natDegree)
    (hI : Irrational P.leadingCoeff) (κ : ℕ → ℝ)
    (happrox : Filter.Tendsto (fun n => κ n - P.eval (n : ℝ))
      Filter.atTop (nhds 0))
    (hnonneg : ∃ B : ℕ, ∀ n, B ≤ n → 0 ≤ κ n)
    (H C : ℕ → ℕ)
    (hstep : ∀ n, start ≤ n →
      max (H (n + h)) (C (n + h)) ≤ max (H n) (C n))
    (hHdiv : ∀ n, start ≤ n →
      Nat.gcd n (d * ⌊κ n⌋₊) ∣ (2 * d) * H n)
    (hCdiv : ∀ n, start ≤ n →
      Nat.gcd n (d * ⌈κ n⌉₊) ∣ (2 * d) * C n) :
    ∃ N : ℕ, ∀ n, N ≤ n → H n = 0 ∧ C n = 0 := by
  let E : ℕ → ℕ := fun n => max (H n) (C n)
  have hEstep : ∀ n, start ≤ n → E (n + h) ≤ E n := hstep
  obtain ⟨M, hM⟩ := recurrence_eventually_bounded E h start hh hEstep
  obtain ⟨p, q, hpM, hqM, hpq, hhpq⟩ :=
    exists_large_coprime_moduli h ((2 * d) * M) hh
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le _) hpM
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hqM
  have hscale : 0 < 2 * d := Nat.mul_pos (by decide) hd
  have hzeros : ∀ b : Fin h, ∃ n : ℕ,
      start ≤ n ∧ n % h = b.val ∧ E n = 0 := by
    intro b
    obtain ⟨n, hn, hnb, hpqn, hpfloor, hqceil⟩ :=
      perturbed_polynomial_crt_selection_nat P hP hI κ happrox hnonneg
        h p q b.val start hh hp hq hpq hhpq b.isLt
    have hpn : p ∣ n := (dvd_mul_right p q).trans hpqn
    have hqn : q ∣ n := (dvd_mul_left q p).trans hpqn
    have hpH : p ∣ (2 * d) * H n :=
      (Nat.dvd_gcd hpn (dvd_mul_of_dvd_right hpfloor d)).trans (hHdiv n hn)
    have hqC : q ∣ (2 * d) * C n :=
      (Nat.dvd_gcd hqn (dvd_mul_of_dvd_right hqceil d)).trans (hCdiv n hn)
    have hHbound : H n ≤ M := (le_max_left (H n) (C n)).trans (hM n hn)
    have hCbound : C n ≤ M := (le_max_right (H n) (C n)).trans (hM n hn)
    have hHzero : H n = 0 :=
      zero_of_scaled_dvd_and_bound (H n) M p (2 * d) hscale hHbound hpM hpH
    have hCzero : C n = 0 :=
      zero_of_scaled_dvd_and_bound (C n) M q (2 * d) hscale hCbound hqM hqC
    exact ⟨n, hn, hnb, by simp only [E, hHzero, hCzero, max_self]⟩
  obtain ⟨N, hN⟩ :=
    eventual_zero_of_recurrence_and_residue_zeros E h start hh hEstep hzeros
  refine ⟨N, ?_⟩
  intro n hn
  have heq : max (H n) (C n) = 0 := hN n hn
  have hH := le_max_left (H n) (C n)
  have hC := le_max_right (H n) (C n)
  omega

end Froberg
