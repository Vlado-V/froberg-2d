import OAI.Geometry.PeriodicTiling.PolynomialWeyl
import Mathlib

/-!
# Arbitrarily late interval hits for polynomial fractional parts

These lemmas specialize the proved polynomial Weyl theorem to arithmetic
progressions.  They establish the interval-selection input used in Section 7,
without assuming a density or equidistribution conclusion as an extra axiom.
-/

namespace Froberg

open Polynomial Set
open scoped Topology

/-- Density on the additive circle gives a hit in any nonempty interval inside
the standard interval of fractional parts. -/
theorem exists_fract_mem_Ioo_of_denseRange
    (f : ℕ → ℝ)
    (hf : DenseRange (fun n => (f n : UnitAddCircle)))
    (u v : ℝ) (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1) :
    ∃ n : ℕ, Int.fract (f n) ∈ Ioo u v := by
  let U : Set UnitAddCircle := (fun x : ℝ => (x : UnitAddCircle)) '' Ioo u v
  have hU : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hne : U.Nonempty := (Set.nonempty_Ioo.mpr huv).image _
  obtain ⟨n, y, hy, heq⟩ := hf.exists_mem_open hU hne
  refine ⟨n, ?_⟩
  have hy0 : y ∈ Ico (0 : ℝ) (0 + 1) := by
    constructor <;> linarith [hy.1, hy.2]
  have hfr : Int.fract (f n) ∈ Ico (0 : ℝ) (0 + 1) := by
    simpa only [zero_add] using
      (show Int.fract (f n) ∈ Ico (0 : ℝ) 1 from
        ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩)
  have hsame : y = Int.fract (f n) :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico hy0 hfr).mp (by simpa using heq)
  simpa only [← hsame] using hy

/-- Polynomial fractional parts on a prescribed arithmetic progression hit
every open interval in `(0,1)` at arbitrarily late natural-number parameters.
Endpoints `0` and `1` are also permitted for the open interval. -/
theorem polynomial_progression_fract_hits
    (P : Polynomial ℝ) (hP : 0 < P.natDegree)
    (hI : Irrational P.leadingCoeff)
    (L A b N : ℕ) (hL : 0 < L) (hA : 0 < A)
    (u v : ℝ) (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1) :
    ∃ s : ℕ, N ≤ s ∧
      Int.fract (P.eval ((b + L * s : ℕ) : ℝ) / (A : ℝ)) ∈ Ioo u v := by
  let R : Polynomial ℝ := C (L : ℝ) * X + C ((b + L * N : ℕ) : ℝ)
  let Q : Polynomial ℝ := C ((A : ℝ)⁻¹) * P.comp R
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hL
  have hA0 : (A : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hA
  have hR : R.natDegree = 1 := Polynomial.natDegree_linear hL0
  have hR0 : R.natDegree ≠ 0 := by omega
  have hQdeg : Q.natDegree = P.natDegree := by
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hA0),
      Polynomial.natDegree_comp, hR, mul_one]
  have hQlc : Q.leadingCoeff =
      (P.leadingCoeff * (L : ℝ) ^ P.natDegree) / (A : ℝ) := by
    dsimp only [Q]
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_comp hR0]
    have hlcR : R.leadingCoeff = (L : ℝ) := Polynomial.leadingCoeff_linear hL0
    rw [hlcR]
    ring
  have hQI : Irrational Q.leadingCoeff := by
    rw [hQlc]
    simpa only [Nat.cast_pow] using
      (hI.mul_natCast (pow_ne_zero _ (Nat.ne_of_gt hL))).div_natCast
        (Nat.ne_of_gt hA)
  have hQD := OAI.PeriodicTilingThree.denseRange_circlePolynomial_of_irrational_leadingCoeff
    Q (by omega) hQI
  obtain ⟨t, ht⟩ := exists_fract_mem_Ioo_of_denseRange
    (fun n => Q.eval (n : ℝ)) hQD u v hu huv hv
  refine ⟨N + t, by omega, ?_⟩
  have heval : Q.eval (t : ℝ) =
      P.eval ((b + L * (N + t) : ℕ) : ℝ) / (A : ℝ) := by
    dsimp only [Q, R]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Nat.cast_add, Nat.cast_mul]
    have harg : (L : ℝ) * t + ((b : ℝ) + (L : ℝ) * N) =
        (b : ℝ) + (L : ℝ) * ((N : ℝ) + t) := by ring
    rw [harg]
    ring
  rwa [← heval]

/-- A fractional part lying in the middle third of a residue interval fixes
both integer roundings even after a perturbation of magnitude less than `1/6`.
The modulus need not be prime. -/
theorem floor_ceil_of_fract_approximation
    (A a : ℕ) (hA : 0 < A) (x y : ℝ)
    (hhit : Int.fract (x / (A : ℝ)) ∈
      Ioo (((a : ℝ) + 1 / 3) / (A : ℝ))
        (((a : ℝ) + 2 / 3) / (A : ℝ)))
    (herr : |y - x| < 1 / 6) :
    ⌊y⌋ = (A : ℤ) * ⌊x / (A : ℝ)⌋ + (a : ℤ) ∧
    ⌈y⌉ = (A : ℤ) * ⌊x / (A : ℝ)⌋ + (a : ℤ) + 1 := by
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hlo := (div_lt_iff₀ hAreal).mp hhit.1
  have hhi := (lt_div_iff₀ hAreal).mp hhit.2
  have hfract : Int.fract (x / (A : ℝ)) * (A : ℝ) =
      x - (A : ℝ) * (⌊x / (A : ℝ)⌋ : ℝ) := by
    dsimp only [Int.fract]
    field_simp
  rw [hfract] at hlo hhi
  obtain ⟨herrlo, herrhi⟩ := abs_lt.mp herr
  constructor
  · apply Int.floor_eq_iff.mpr
    constructor <;> push_cast <;> linarith
  · apply Int.ceil_eq_iff.mpr
    constructor <;> push_cast <;> linarith

/-- The polynomial interval hits persist under any eventually `1/6`-small
perturbation, with an exact common integer quotient for floor and ceiling. -/
theorem perturbed_polynomial_progression_roundings
    (P : Polynomial ℝ) (hP : 0 < P.natDegree)
    (hI : Irrational P.leadingCoeff) (κ : ℕ → ℝ)
    (happrox : ∃ B : ℕ, ∀ n, B ≤ n → |κ n - P.eval (n : ℝ)| < 1 / 6)
    (L A b N a : ℕ) (hL : 0 < L) (hA : 0 < A) (ha : a < A) :
    ∃ s : ℕ, N ≤ s ∧ ∃ t : ℤ,
      ⌊κ (b + L * s)⌋ = (A : ℤ) * t + (a : ℤ) ∧
      ⌈κ (b + L * s)⌉ = (A : ℤ) * t + (a : ℤ) + 1 := by
  obtain ⟨B, hB⟩ := happrox
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have ha1 : (a : ℝ) + 1 ≤ (A : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr ha)
  have hu : (0 : ℝ) ≤ ((a : ℝ) + 1 / 3) / (A : ℝ) := by positivity
  have huv : ((a : ℝ) + 1 / 3) / (A : ℝ) <
      ((a : ℝ) + 2 / 3) / (A : ℝ) := by
    apply (div_lt_div_iff_of_pos_right hAreal).mpr
    norm_num
  have hv : ((a : ℝ) + 2 / 3) / (A : ℝ) ≤ 1 := by
    apply (div_le_one hAreal).mpr
    linarith
  obtain ⟨s, hs, hhit⟩ := polynomial_progression_fract_hits
    P hP hI L A b (max N B) hL hA
    (((a : ℝ) + 1 / 3) / (A : ℝ))
    (((a : ℝ) + 2 / 3) / (A : ℝ)) hu huv hv
  have hNs : N ≤ s := (le_max_left N B).trans hs
  have hBs : B ≤ s := (le_max_right N B).trans hs
  have hBn : B ≤ b + L * s := by nlinarith
  refine ⟨s, hNs, ⌊P.eval ((b + L * s : ℕ) : ℝ) / (A : ℝ)⌋, ?_⟩
  exact floor_ceil_of_fract_approximation A a hA _ _ hhit (hB _ hBn)

/-- The same exact rounding conclusion follows from convergence of the
approximation error to zero. -/
theorem perturbed_polynomial_progression_roundings_of_tendsto
    (P : Polynomial ℝ) (hP : 0 < P.natDegree)
    (hI : Irrational P.leadingCoeff) (κ : ℕ → ℝ)
    (happrox : Filter.Tendsto (fun n => κ n - P.eval (n : ℝ))
      Filter.atTop (nhds 0))
    (L A b N a : ℕ) (hL : 0 < L) (hA : 0 < A) (ha : a < A) :
    ∃ s : ℕ, N ≤ s ∧ ∃ t : ℤ,
      ⌊κ (b + L * s)⌋ = (A : ℤ) * t + (a : ℤ) ∧
      ⌈κ (b + L * s)⌉ = (A : ℤ) * t + (a : ℤ) + 1 := by
  apply perturbed_polynomial_progression_roundings P hP hI κ _ L A b N a hL hA ha
  obtain ⟨B, hB⟩ := (Metric.tendsto_atTop.mp happrox) (1 / 6) (by norm_num)
  refine ⟨B, ?_⟩
  intro n hn
  simpa only [Real.dist_eq, sub_zero] using hB n hn

/-- A chosen residue satisfying two divisibility conditions makes the two
adjacent roundings divisible by their respective moduli, arbitrarily late
along the chosen progression. -/
theorem perturbed_polynomial_progression_divisibility
    (P : Polynomial ℝ) (hP : 0 < P.natDegree)
    (hI : Irrational P.leadingCoeff) (κ : ℕ → ℝ)
    (happrox : Filter.Tendsto (fun n => κ n - P.eval (n : ℝ))
      Filter.atTop (nhds 0))
    (L A b N a p q : ℕ) (hL : 0 < L) (hA : 0 < A) (ha : a < A)
    (hpA : p ∣ A) (hpa : p ∣ a) (hqA : q ∣ A) (hqa : q ∣ a + 1) :
    ∃ s : ℕ, N ≤ s ∧
      (p : ℤ) ∣ ⌊κ (b + L * s)⌋ ∧ (q : ℤ) ∣ ⌈κ (b + L * s)⌉ := by
  obtain ⟨s, hs, t, hf, hc⟩ := perturbed_polynomial_progression_roundings_of_tendsto
    P hP hI κ happrox L A b N a hL hA ha
  refine ⟨s, hs, ?_, ?_⟩
  · rw [hf]
    exact dvd_add (dvd_mul_of_dvd_left (by exact_mod_cast hpA) t)
      (by exact_mod_cast hpa)
  · rw [hc, add_assoc]
    exact dvd_add (dvd_mul_of_dvd_left (by exact_mod_cast hqA) t)
      (by exact_mod_cast hqa)

/-- Chinese remaindering supplies a residue whose lower and upper adjacent
integers are divisible by the two chosen coprime moduli. -/
theorem exists_adjacent_divisible_residue
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q) :
    ∃ a : ℕ, a < p * q ∧ p ∣ a ∧ q ∣ a + 1 := by
  let a := Nat.chineseRemainder hpq 0 (q - 1)
  refine ⟨a.val, Nat.chineseRemainder_lt_mul hpq 0 (q - 1)
    (Nat.ne_of_gt hp) (Nat.ne_of_gt hq), ?_, ?_⟩
  · exact Nat.modEq_zero_iff_dvd.mp a.property.1
  · have hh := a.property.2.add_right 1
    have hq1 : q - 1 + 1 = q := by omega
    rw [hq1] at hh
    exact Nat.modEq_zero_iff_dvd.mp
      (hh.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl q)))

/-- Full arithmetic selection from the manuscript: every residue class modulo
`h` contains arbitrarily large indices divisible by `p*q` at which the lower
and upper rounded values are divisible by `p` and `q`, respectively.  The
moduli need only be positive and coprime as stated; primality is unnecessary. -/
theorem perturbed_polynomial_crt_selection
    (P : Polynomial ℝ) (hP : 0 < P.natDegree)
    (hI : Irrational P.leadingCoeff) (κ : ℕ → ℝ)
    (happrox : Filter.Tendsto (fun n => κ n - P.eval (n : ℝ))
      Filter.atTop (nhds 0))
    (h p q b N : ℕ) (hh : 0 < h) (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (hhpq : Nat.Coprime h (p * q)) (hb : b < h) :
    ∃ n : ℕ, N ≤ n ∧ n % h = b ∧ p * q ∣ n ∧
      (p : ℤ) ∣ ⌊κ n⌋ ∧ (q : ℤ) ∣ ⌈κ n⌉ := by
  let base := Nat.chineseRemainder hhpq b 0
  obtain ⟨a, ha, hpa, hqa⟩ := exists_adjacent_divisible_residue p q hp hq hpq
  have hprod : 0 < p * q := Nat.mul_pos hp hq
  have hL : 0 < h * (p * q) := Nat.mul_pos hh hprod
  obtain ⟨s, hs, hfloor, hceil⟩ := perturbed_polynomial_progression_divisibility
    P hP hI κ happrox (h * (p * q)) (p * q) base.val N a p q
    hL hprod ha (dvd_mul_right p q) hpa (dvd_mul_left q p) hqa
  refine ⟨base.val + (h * (p * q)) * s, ?_, ?_, ?_, hfloor, hceil⟩
  · nlinarith
  · have hbmod : base.val % h = b := Nat.mod_eq_of_modEq base.property.1 hb
    have hdvd : h ∣ (h * (p * q)) * s :=
      dvd_mul_of_dvd_left (dvd_mul_right h (p * q)) s
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, add_zero, Nat.mod_mod, hbmod]
  · exact dvd_add (Nat.modEq_zero_iff_dvd.mp base.property.2)
      (dvd_mul_of_dvd_left (dvd_mul_left (p * q) h) s)

/-- Natural-number floor and ceiling version of the CRT selection.  Eventual
nonnegativity is enough for applying the result to critical generator counts. -/
theorem perturbed_polynomial_crt_selection_nat
    (P : Polynomial ℝ) (hP : 0 < P.natDegree)
    (hI : Irrational P.leadingCoeff) (κ : ℕ → ℝ)
    (happrox : Filter.Tendsto (fun n => κ n - P.eval (n : ℝ))
      Filter.atTop (nhds 0))
    (hnonneg : ∃ B : ℕ, ∀ n, B ≤ n → 0 ≤ κ n)
    (h p q b N : ℕ) (hh : 0 < h) (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (hhpq : Nat.Coprime h (p * q)) (hb : b < h) :
    ∃ n : ℕ, N ≤ n ∧ n % h = b ∧ p * q ∣ n ∧
      p ∣ ⌊κ n⌋₊ ∧ q ∣ ⌈κ n⌉₊ := by
  obtain ⟨B, hB⟩ := hnonneg
  obtain ⟨n, hn, hnb, hndvd, hnf, hnc⟩ := perturbed_polynomial_crt_selection
    P hP hI κ happrox h p q b (max N B) hh hp hq hpq hhpq hb
  have hκ : 0 ≤ κ n := hB n ((le_max_right N B).trans hn)
  refine ⟨n, (le_max_left N B).trans hn, hnb, hndvd, ?_, ?_⟩
  · rw [← Int.natCast_floor_eq_floor hκ] at hnf
    exact_mod_cast hnf
  · rw [← Int.natCast_ceil_eq_ceil hκ] at hnc
    exact_mod_cast hnc

end Froberg
