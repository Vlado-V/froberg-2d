import Froberg.Graded
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Data.Nat.Choose.Vandermonde

/-! Weighted monomial incidence for an elementary replacement of condensed
Macaulay growth in the eventual prefix argument. -/
noncomputable section
namespace Froberg.MonomialExpansion
open Finset PowerSeries

/-- All degree-`d` exponent vectors in `n` variables. -/
def exponents (n d : ℕ) : Finset (Fin n →₀ ℕ) := finsuppAntidiag univ d

@[simp] theorem mem_exponents {n d : ℕ} {a : Fin n →₀ ℕ} :
    a ∈ exponents n d ↔ a.degree = d := by
  simp only [exponents, Finset.mem_finsuppAntidiag', Finset.subset_univ, and_true]
  rfl

/-- Number of ways to select the source multiset inside the target multiset. -/
def weight {n : ℕ} (b a : Fin n →₀ ℕ) : ℕ := ∏ i, (b i).choose (a i)

theorem weight_pos_iff {n : ℕ} (b a : Fin n →₀ ℕ) : 0 < weight b a ↔ a ≤ b := by
  simp only [Nat.pos_iff_ne_zero, weight, Finset.prod_ne_zero_iff, Finset.mem_univ,
    forall_true_left, Nat.choose_ne_zero_iff, Finsupp.le_def]

theorem weight_ne_zero_iff {n : ℕ} (b a : Fin n →₀ ℕ) : weight b a ≠ 0 ↔ a ≤ b := by
  rw [← Nat.pos_iff_ne_zero, weight_pos_iff]

/-- The weighted number of degree-`e` divisors depends only on total degree. -/
theorem sum_weight_sources {n : ℕ} (b : Fin n →₀ ℕ) (e : ℕ) :
    ∑ a ∈ exponents n e, weight b a = b.degree.choose e := by
  let f : Fin n → PowerSeries ℤ := fun i =>
    (((Polynomial.X + 1 : Polynomial ℤ) ^ b i : Polynomial ℤ) : PowerSeries ℤ)
  have hc (i : Fin n) (j : ℕ) : coeff j (f i) = ((b i).choose j : ℤ) := by
    change PowerSeries.coeff j (((Polynomial.X + 1 : Polynomial ℤ) ^ b i : Polynomial ℤ) : PowerSeries ℤ) = _
    rw [Polynomial.coeff_coe, Polynomial.coeff_X_add_one_pow]
  have hp : ∏ i, f i =
      (((Polynomial.X + 1 : Polynomial ℤ) ^ b.degree : Polynomial ℤ) : PowerSeries ℤ) := by
    simp only [f, Polynomial.coe_pow]
    rw [Finset.prod_pow_eq_pow_sum]
    rw [Finsupp.degree_eq_sum b]
  have h := PowerSeries.coeff_prod f e (univ : Finset (Fin n))
  rw [hp] at h
  simp only [hc, Polynomial.coeff_coe, Polynomial.coeff_X_add_one_pow] at h
  have hh : (∑ a ∈ exponents n e, weight b a : ℕ) = b.degree.choose e := by
    exact_mod_cast h.symm
  exact hh

/-- The weighted number of extensions by a fixed extra degree is independent
of the shape of the source monomial. -/
theorem sum_weight_extensions {n : ℕ} (hn : 0 < n) (a : Fin n →₀ ℕ) (d : ℕ) :
    ∑ c ∈ exponents n d, weight (a + c) a = (n + a.degree + d - 1).choose d := by
  let g : PowerSeries ℤ := mk 1
  let f : Fin n → PowerSeries ℤ := fun i => g ^ (a i + 1)
  have hc (i : Fin n) (j : ℕ) : coeff j (f i) = ((a i + j).choose (a i) : ℤ) := by
    change PowerSeries.coeff j ((mk 1 : PowerSeries ℤ) ^ (a i + 1)) = _
    rw [mk_one_pow_eq_mk_choose_add, coeff_mk]
  have hs : ∑ i : Fin n, (a i + 1) = a.degree + n := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    congr 1
    exact (Finsupp.degree_eq_sum _).symm
  have hp : ∏ i, f i = g ^ (a.degree + n) := by
    simp only [f]
    rw [Finset.prod_pow_eq_pow_sum, hs]
  have h := PowerSeries.coeff_prod f d (univ : Finset (Fin n))
  rw [hp, show a.degree + n = (a.degree + n - 1) + 1 by omega,
    show g = (mk 1 : PowerSeries ℤ) from rfl, mk_one_pow_eq_mk_choose_add, coeff_mk] at h
  simp only [hc] at h
  have hh : (∑ c ∈ exponents n d, weight (a + c) a : ℕ) =
      (a.degree + n - 1 + d).choose (a.degree + n - 1) := by
    exact_mod_cast h.symm
  rw [hh]
  rw [show n + a.degree + d - 1 = a.degree + n - 1 + d by omega]
  exact Nat.choose_symm_of_eq_add (n := a.degree + n - 1 + d)
    (a := a.degree + n - 1) (b := d) rfl

end Froberg.MonomialExpansion
