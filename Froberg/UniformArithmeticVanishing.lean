module

public import Froberg.Recurrence
public import Froberg.PolynomialHits

@[expose] public section

/-!
# Uniform arithmetic vanishing with one excluded prime

The bounds, recurrence, and approximation in this file are uniform over an
arbitrary index type.  The divisibility statements may exclude the prime
characteristic attached to each index.  Three pairwise coprime moduli leave
two usable moduli at every index.  The CRT dimensions for all three pairs
are selected before the index, so the final threshold is uniform.
-/

namespace Froberg

open Polynomial
open scoped Topology

/-- Three arbitrarily large pairwise coprime moduli, all coprime to a given
positive recurrence step.  They need not be prime. -/
theorem exists_three_large_coprime_moduli (h B : ℕ) (hh : 0 < h) :
    ∃ a b c : ℕ, B < a ∧ B < b ∧ B < c ∧
      Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime b c ∧
      Nat.Coprime h a ∧ Nat.Coprime h b ∧ Nat.Coprime h c := by
  let a := h * (B + 1) + 1
  let b := h * a + 1
  let c := h * (a * b) + 1
  have ha : B < a := by dsimp only [a]; nlinarith
  have hb : B < b := by dsimp only [b]; nlinarith
  have hc : B < c := by
    have ha0 : 0 < a := (Nat.zero_le B).trans_lt ha
    have hmul := Nat.le_mul_of_pos_left b (Nat.mul_pos hh ha0)
    dsimp only [c]
    rw [← Nat.mul_assoc]
    omega
  have hab : Nat.Coprime a b := by
    dsimp only [b]
    rw [Nat.coprime_mul_right_add_right]
    exact Nat.coprime_one_right a
  have hac : Nat.Coprime a c := by
    have hc' : c = (h * b) * a + 1 := by dsimp only [c]; ring
    rw [hc', Nat.coprime_mul_right_add_right]
    exact Nat.coprime_one_right a
  have hbc : Nat.Coprime b c := by
    dsimp only [c]
    rw [← Nat.mul_assoc, Nat.coprime_mul_right_add_right]
    exact Nat.coprime_one_right b
  have hha : Nat.Coprime h a := by
    dsimp only [a]
    rw [Nat.coprime_mul_left_add_right]
    exact Nat.coprime_one_right h
  have hhb : Nat.Coprime h b := by
    dsimp only [b]
    rw [Nat.coprime_mul_left_add_right]
    exact Nat.coprime_one_right h
  have hhc : Nat.Coprime h c := by
    dsimp only [c]
    rw [Nat.coprime_mul_left_add_right]
    exact Nat.coprime_one_right h
  exact ⟨a, b, c, ha, hb, hc, hab, hac, hbc, hha, hhb, hhc⟩

/-- At most one of three pairwise coprime moduli is unusable in a prime
characteristic.  Characteristic zero excludes none. -/
theorem two_coprime_moduli_avoid_characteristic (a b c p : ℕ)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hp : p = 0 ∨ Nat.Prime p) :
    ((p = 0 ∨ Nat.Coprime a p) ∧ (p = 0 ∨ Nat.Coprime b p)) ∨
    ((p = 0 ∨ Nat.Coprime a p) ∧ (p = 0 ∨ Nat.Coprime c p)) ∨
    ((p = 0 ∨ Nat.Coprime b p) ∧ (p = 0 ∨ Nat.Coprime c p)) := by
  rcases hp with hp | hp
  · exact Or.inl ⟨Or.inl hp, Or.inl hp⟩
  by_cases ha : Nat.Coprime a p
  · by_cases hb : Nat.Coprime b p
    · exact Or.inl ⟨Or.inr ha, Or.inr hb⟩
    · have hpb : p ∣ b := hp.dvd_iff_not_coprime.mpr (fun h => hb h.symm)
      have hc : Nat.Coprime c p := Nat.Coprime.coprime_dvd_right hpb hbc.symm
      exact Or.inr (Or.inl ⟨Or.inr ha, Or.inr hc⟩)
  · have hpa : p ∣ a := hp.dvd_iff_not_coprime.mpr (fun h => ha h.symm)
    have hb : Nat.Coprime b p := Nat.Coprime.coprime_dvd_right hpa hab.symm
    have hc : Nat.Coprime c p := Nat.Coprime.coprime_dvd_right hpa hac.symm
    exact Or.inr (Or.inr ⟨Or.inr hb, Or.inr hc⟩)

/-- One fixed pair of usable moduli gives a threshold uniform over every
index where the pair's divisibility statements apply. -/
theorem uniform_arithmetic_vanishing_for_pair {ι : Type*}
    (d h start M a b : ℕ) (hd : 0 < d) (hh : 0 < h)
    (ha : (2 * d) * M < a) (hb : (2 * d) * M < b)
    (hab : Nat.Coprime a b) (hhab : Nat.Coprime h (a * b))
    (P : Polynomial ℝ) (hP : 0 < P.natDegree)
    (hI : Irrational P.leadingCoeff) (κ : ℕ → ℝ)
    (happrox : Filter.Tendsto (fun n => κ n - P.eval (n : ℝ))
      Filter.atTop (nhds 0))
    (hnonneg : ∃ B : ℕ, ∀ n, B ≤ n → 0 ≤ κ n)
    (H C : ι → ℕ → ℕ) (good : ι → Prop)
    (hstep : ∀ i n, start ≤ n →
      max (H i (n + h)) (C i (n + h)) ≤ max (H i n) (C i n))
    (hbound : ∀ i n, start ≤ n → max (H i n) (C i n) ≤ M)
    (hHdiv : ∀ i, good i → ∀ n, start ≤ n →
      a ∣ Nat.gcd n (d * ⌊κ n⌋₊) → a ∣ (2 * d) * H i n)
    (hCdiv : ∀ i, good i → ∀ n, start ≤ n →
      b ∣ Nat.gcd n (d * ⌈κ n⌉₊) → b ∣ (2 * d) * C i n) :
    ∃ N : ℕ, ∀ i, good i → ∀ n, N ≤ n → H i n = 0 ∧ C i n = 0 := by
  classical
  have ha0 : 0 < a := lt_of_le_of_lt (Nat.zero_le _) ha
  have hb0 : 0 < b := lt_of_le_of_lt (Nat.zero_le _) hb
  have hnodes : ∀ r : Fin h, ∃ n : ℕ,
      start ≤ n ∧ n % h = r.val ∧ a * b ∣ n ∧
        a ∣ ⌊κ n⌋₊ ∧ b ∣ ⌈κ n⌉₊ := by
    intro r
    exact perturbed_polynomial_crt_selection_nat P hP hI κ happrox hnonneg
      h a b r.val start hh ha0 hb0 hab hhab r.isLt
  choose w hwstart hwmod hwmul hwfloor hwceil using hnodes
  refine ⟨Finset.univ.sup w, ?_⟩
  intro i hi n hn
  let r : Fin h := ⟨n % h, Nat.mod_lt n hh⟩
  have hwr : w r ≤ n := (Finset.le_sup (f := w) (Finset.mem_univ r)).trans hn
  have hcong : Nat.ModEq h (w r) n := hwmod r
  obtain ⟨t, ht⟩ := hcong.dvd'
  have heq : w r + t * h = n := by
    rw [Nat.mul_comm t h]
    omega
  have haH : a ∣ (2 * d) * H i (w r) := hHdiv i hi (w r) (hwstart r)
    (Nat.dvd_gcd ((dvd_mul_right a b).trans (hwmul r))
      (dvd_mul_of_dvd_right (hwfloor r) d))
  have hbC : b ∣ (2 * d) * C i (w r) := hCdiv i hi (w r) (hwstart r)
    (Nat.dvd_gcd ((dvd_mul_left b a).trans (hwmul r))
      (dvd_mul_of_dvd_right (hwceil r) d))
  have hscale : 0 < 2 * d := Nat.mul_pos (by decide) hd
  have hHzero : H i (w r) = 0 := zero_of_scaled_dvd_and_bound
    (H i (w r)) M a (2 * d) hscale
    ((le_max_left _ _).trans (hbound i (w r) (hwstart r))) ha haH
  have hCzero : C i (w r) = 0 := zero_of_scaled_dvd_and_bound
    (C i (w r)) M b (2 * d) hscale
    ((le_max_right _ _).trans (hbound i (w r) (hwstart r))) hb hbC
  have hzero : max (H i n) (C i n) = 0 := by
    rw [← heq]
    exact recurrence_zero_propagates (fun m => max (H i m) (C i m))
      h start (hstep i) (w r) (hwstart r) (by simp [hHzero, hCzero]) t
  exact ⟨Nat.eq_zero_of_le_zero ((le_max_left _ _).trans hzero.le),
    Nat.eq_zero_of_le_zero ((le_max_right _ _).trans hzero.le)⟩

/-- A common bound and recurrence force simultaneous eventual vanishing for
an arbitrary family.  Divisibility is required only for divisors coprime to
the index's prime characteristic, or for all divisors in characteristic zero.
The threshold does not depend on the index or its characteristic. -/
theorem uniform_arithmetic_eventual_vanishing {ι : Type*}
    (d h start M : ℕ) (hd : 0 < d) (hh : 0 < h)
    (P : Polynomial ℝ) (hP : 0 < P.natDegree)
    (hI : Irrational P.leadingCoeff) (κ : ℕ → ℝ)
    (happrox : Filter.Tendsto (fun n => κ n - P.eval (n : ℝ))
      Filter.atTop (nhds 0))
    (hnonneg : ∃ B : ℕ, ∀ n, B ≤ n → 0 ≤ κ n)
    (H C : ι → ℕ → ℕ) (p : ι → ℕ)
    (hp : ∀ i, p i = 0 ∨ Nat.Prime (p i))
    (hstep : ∀ i n, start ≤ n →
      max (H i (n + h)) (C i (n + h)) ≤ max (H i n) (C i n))
    (hbound : ∀ i n, start ≤ n → max (H i n) (C i n) ≤ M)
    (hHdiv : ∀ i n, start ≤ n → ∀ ℓ, ℓ ∣ Nat.gcd n (d * ⌊κ n⌋₊) →
      (p i = 0 ∨ Nat.Coprime ℓ (p i)) → ℓ ∣ (2 * d) * H i n)
    (hCdiv : ∀ i n, start ≤ n → ∀ ℓ, ℓ ∣ Nat.gcd n (d * ⌈κ n⌉₊) →
      (p i = 0 ∨ Nat.Coprime ℓ (p i)) → ℓ ∣ (2 * d) * C i n) :
    ∃ N : ℕ, ∀ i n, N ≤ n → H i n = 0 ∧ C i n = 0 := by
  have hpair (a b : ℕ) (ha : (2 * d) * M < a) (hb : (2 * d) * M < b)
      (hab : Nat.Coprime a b) (hha : Nat.Coprime h a) (hhb : Nat.Coprime h b) :
      ∃ N : ℕ, ∀ i, (p i = 0 ∨ Nat.Coprime a (p i)) →
        (p i = 0 ∨ Nat.Coprime b (p i)) →
          ∀ n, N ≤ n → H i n = 0 ∧ C i n = 0 := by
    obtain ⟨N, hN⟩ := uniform_arithmetic_vanishing_for_pair d h start M a b hd hh
      ha hb hab (hha.mul_right hhb) P hP hI κ happrox hnonneg H C
      (fun i => (p i = 0 ∨ Nat.Coprime a (p i)) ∧
        (p i = 0 ∨ Nat.Coprime b (p i))) hstep hbound
      (fun i hi n hn hdiv => hHdiv i n hn a hdiv hi.1)
      (fun i hi n hn hdiv => hCdiv i n hn b hdiv hi.2)
    exact ⟨N, fun i hi hj => hN i ⟨hi, hj⟩⟩
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc, hha, hhb, hhc⟩ :=
    exists_three_large_coprime_moduli h ((2 * d) * M) hh
  obtain ⟨Nab, hNab⟩ := hpair a b ha hb hab hha hhb
  obtain ⟨Nac, hNac⟩ := hpair a c ha hc hac hha hhc
  obtain ⟨Nbc, hNbc⟩ := hpair b c hb hc hbc hhb hhc
  refine ⟨max Nab (max Nac Nbc), ?_⟩
  intro i n hn
  rcases two_coprime_moduli_avoid_characteristic a b c (p i) hab hac hbc (hp i) with
    hi | hi | hi
  · exact hNab i hi.1 hi.2 n (by omega)
  · exact hNac i hi.1 hi.2 n (by omega)
  · exact hNbc i hi.1 hi.2 n (by omega)

/-- It suffices to bound the indexed defects uniformly on one initial
recurrence window.  The recurrence supplies the common bound on the tail. -/
theorem uniform_arithmetic_eventual_vanishing_of_window {ι : Type*}
    (d h start M : ℕ) (hd : 0 < d) (hh : 0 < h)
    (P : Polynomial ℝ) (hP : 0 < P.natDegree)
    (hI : Irrational P.leadingCoeff) (κ : ℕ → ℝ)
    (happrox : Filter.Tendsto (fun n => κ n - P.eval (n : ℝ))
      Filter.atTop (nhds 0))
    (hnonneg : ∃ B : ℕ, ∀ n, B ≤ n → 0 ≤ κ n)
    (H C : ι → ℕ → ℕ) (p : ι → ℕ)
    (hp : ∀ i, p i = 0 ∨ Nat.Prime (p i))
    (hstep : ∀ i n, start ≤ n →
      max (H i (n + h)) (C i (n + h)) ≤ max (H i n) (C i n))
    (hwindow : ∀ i n, start ≤ n → n < start + h → max (H i n) (C i n) ≤ M)
    (hHdiv : ∀ i n, start ≤ n → ∀ ℓ, ℓ ∣ Nat.gcd n (d * ⌊κ n⌋₊) →
      (p i = 0 ∨ Nat.Coprime ℓ (p i)) → ℓ ∣ (2 * d) * H i n)
    (hCdiv : ∀ i n, start ≤ n → ∀ ℓ, ℓ ∣ Nat.gcd n (d * ⌈κ n⌉₊) →
      (p i = 0 ∨ Nat.Coprime ℓ (p i)) → ℓ ∣ (2 * d) * C i n) :
    ∃ N : ℕ, ∀ i n, N ≤ n → H i n = 0 ∧ C i n = 0 := by
  apply uniform_arithmetic_eventual_vanishing d h start M hd hh P hP hI κ
    happrox hnonneg H C p hp hstep _ hHdiv hCdiv
  intro i
  exact recurrence_bound_from_window (fun n => max (H i n) (C i n))
    h start M hh (hstep i) (hwindow i)

end Froberg
