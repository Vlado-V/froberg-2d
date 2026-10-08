import Quartic.Homogeneous
import Mathlib.RingTheory.Nullstellensatz

/-!
# A finite homogeneous certificate for an empty projective fiber

No common nonzero zero over an algebraically closed extension implies that
all sufficiently high homogeneous forms lie in the generator ideal. The
finite-degree multiplication certificate is derived from this conclusion,
not assumed as an extra hypothesis.
-/
noncomputable section
namespace Quartic.HomogeneousNullstellensatz
open Module MvPolynomial
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
variable {s r : ℕ}

/-- Geometric emptiness gives a positive power of each variable in the actual ideal. -/
theorem exists_variable_powers (f : Fin r → Poly K s)
    (hempty : ∀ x : Fin s → L, (∀ j, aeval x (f j) = 0) → x = 0) :
    ∃ n : Fin s → ℕ, (∀ i, 0 < n i) ∧
      ∀ i, (X i : Poly K s) ^ n i ∈ Ideal.span (Set.range f) := by
  have hrad (i : Fin s) : (X i : Poly K s) ∈ (Ideal.span (Set.range f)).radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := L)]
    intro x hx
    have hzero : x = 0 := hempty x (fun j => hx (f j) (Ideal.subset_span ⟨j,rfl⟩))
    simp [hzero]
  have hp (i : Fin s) : ∃ n : ℕ, 0 < n ∧ (X i : Poly K s)^n ∈ Ideal.span (Set.range f) := by
    obtain ⟨n,hn⟩ := (Ideal.mem_radical_iff).mp (hrad i)
    refine ⟨n+1,by omega,?_⟩
    rw [pow_succ]
    exact Ideal.mul_mem_right _ _ hn
  choose n hn hmem using hp
  exact ⟨n,hn,hmem⟩

/-- A sufficiently large exponent contains one of the prescribed positive powers. -/
theorem exists_large_coordinate (n : Fin s → ℕ) (_hn : ∀ i, 0 < n i)
    (e : Fin s →₀ ℕ) (he : e.degree = 1 + ∑ i, (n i-1)) :
    ∃ i, n i ≤ e i := by
  classical
  by_contra h
  push Not at h
  have hsum : ∑ i, e i ≤ ∑ i, (n i-1) :=
    Finset.sum_le_sum (fun i _ => by have hi := h i; omega)
  rw [← Finsupp.degree_eq_sum] at hsum
  omega

/-- Divisibility by one coordinate power puts the whole monomial in the ideal. -/
theorem monomial_mem_of_power_mem (I : Ideal (Poly K s)) (e : Fin s →₀ ℕ) (i : Fin s)
    (n : ℕ) (hni : n ≤ e i) (hpow : (X i : Poly K s)^n ∈ I) (c : K) :
    monomial e c ∈ I := by
  classical
  have hle : Finsupp.single i n ≤ e := by
    intro j
    by_cases hj : j=i
    · subst j; simpa using hni
    · simp [Finsupp.single_eq_of_ne hj]
  have hid : monomial e c = monomial (e-Finsupp.single i n) c * (X i : Poly K s)^n := by
    rw [X_pow_eq_monomial, monomial_mul_monomial, mul_one, tsub_add_cancel_of_le hle]
  rw [hid]
  exact I.mul_mem_left _ hpow

/-- A genuinely derived finite degree contains every homogeneous form in the ideal. -/
theorem exists_degree_all_forms_mem (f : Fin r → Poly K s)
    (hempty : ∀ x : Fin s → L, (∀ j, aeval x (f j) = 0) → x = 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ p : Forms K s N, p.val ∈ Ideal.span (Set.range f) := by
  classical
  obtain ⟨n,hn,hmem⟩ := exists_variable_powers f hempty
  refine ⟨1+∑ i, (n i-1), by omega, ?_⟩
  intro p
  rw [← p.val.support_sum_monomial_coeff]
  apply Ideal.sum_mem
  intro e he
  have hedeg : e.degree = 1+∑ i, (n i-1) := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using p.property (mem_support_iff.mp he)
  obtain ⟨i,hi⟩ := exists_large_coordinate n hn e hedeg
  exact monomial_mem_of_power_mem _ e i (n i) hi (hmem i) _

/-- Taking a homogeneous component of a product by a homogeneous generator. -/
theorem component_mul_homogeneous {d N : ℕ} (u : Poly K s) (f : Forms K s d)
    (hd : d ≤ N) :
    homogeneousComponent N (u*f.val) = homogeneousComponent (N-d) u * f.val := by
  classical
  induction u using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [homogeneousComponent_of_mem ((isHomogeneous_monomial c rfl).mul f.property),
      homogeneousComponent_of_mem (isHomogeneous_monomial c rfl)]
    by_cases he : N=e.degree+d
    · have he' : N-d=e.degree := by omega
      simp [he]
    · have he' : N-d≠e.degree := by omega
      simp [he,he']
  | add u v hu hv => simp only [add_mul, map_add, hu,hv]

/-- Generators of degree greater than N make no contribution in degree N. -/
theorem component_mul_homogeneous_of_lt {d N : ℕ} (u : Poly K s) (f : Forms K s d)
    (hd : N < d) : homogeneousComponent N (u*f.val) = 0 := by
  classical
  induction u using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [homogeneousComponent_of_mem ((isHomogeneous_monomial c rfl).mul f.property)]
    simp [show N ≠ e.degree+d by omega]
  | add u v hu hv => simp only [add_mul, map_add,hu,hv,add_zero]

end Quartic.HomogeneousNullstellensatz
