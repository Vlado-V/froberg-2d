module

public import Quartic.Homogeneous
public import Mathlib.Data.Sym.Sym2.Order
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-!
# Bounded symmetric bivariate polynomials

The actual polynomial subspace is defined by a rectangular support bound and
symmetry of coefficients. Its coordinates are indexed by sorted pairs, so its
dimension is `choose (p+1) 2` over every field, including characteristic two.
-/

namespace Quartic.ConvolutionSymmetric

noncomputable section

open MvPolynomial

variable {K : Type*} [Field K] {p : ℕ}

abbrev PairIndex (p : ℕ) := {ij : Fin p × Fin p // ij.1 ≤ ij.2}

def sortedPair (i j : Fin p) : PairIndex p :=
  ⟨(min i j, max i j), min_le_max⟩

@[simp] theorem sortedPair_swap (i j : Fin p) : sortedPair i j = sortedPair j i := by
  apply Subtype.ext
  simp [sortedPair, min_comm, max_comm]

theorem sortedPair_of_le (i j : Fin p) (h : i ≤ j) :
    sortedPair i j = ⟨(i, j), h⟩ := by
  apply Subtype.ext
  simp [sortedPair, min_eq_left h, max_eq_right h]

def pairExponent (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b

@[simp] theorem pairExponent_zero (a b : ℕ) : pairExponent a b 0 = a := by
  simp [pairExponent]

@[simp] theorem pairExponent_one (a b : ℕ) : pairExponent a b 1 = b := by
  simp [pairExponent]

theorem pairExponent_eq_iff (a b c d : ℕ) :
    pairExponent a b = pairExponent c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun e : Fin 2 →₀ ℕ => e 0) h,
      by simpa using congrArg (fun e : Fin 2 →₀ ℕ => e 1) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem pairExponent_all (e : Fin 2 →₀ ℕ) : pairExponent (e 0) (e 1) = e := by
  ext i
  fin_cases i <;> simp

/-- An actual polynomial submodule: support lies in the square of exponents
`0,...,p-1`, and the two coefficient indices are interchangeable. -/
def symmetricSpace (K : Type*) [Field K] (p : ℕ) : Submodule K (Quartic.Poly K 2) where
  carrier := {f | (∀ e : Fin 2 →₀ ℕ, p ≤ e 0 ∨ p ≤ e 1 → f.coeff e = 0) ∧
    ∀ i j : Fin p, f.coeff (pairExponent i.val j.val) = f.coeff (pairExponent j.val i.val)}
  zero_mem' := by simp
  add_mem' hf hg := by
    constructor
    · intro e he
      simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf.1 e he, hg.1 e he, add_zero]
    · intro i j
      simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf.2 i j, hg.2 i j]
  smul_mem' c f hf := by
    constructor
    · intro e he
      simp only [coeff_smul, hf.1 e he, smul_zero]
    · intro i j
      simp only [coeff_smul, hf.2 i j]

/-- Convert sorted-pair coefficient arrays into genuine symmetric polynomials. -/
def fromCoefficients (K : Type*) [Field K] (p : ℕ) :
    (PairIndex p → K) →ₗ[K] Quartic.Poly K 2 :=
  ∑ i : Fin p, ∑ j : Fin p,
    (MvPolynomial.monomial (pairExponent i.val j.val)).comp (LinearMap.proj (sortedPair i j))

@[simp] theorem fromCoefficients_apply (c : PairIndex p → K) :
    fromCoefficients K p c = ∑ i : Fin p, ∑ j : Fin p,
      monomial (pairExponent i.val j.val) (c (sortedPair i j)) := by
  simp [fromCoefficients]

/-- Coefficient extraction is a left inverse to the coordinate construction. -/
theorem fromCoefficients_coeff (c : PairIndex p → K) (i j : Fin p) :
    (fromCoefficients K p c).coeff (pairExponent i.val j.val) = c (sortedPair i j) := by
  classical
  simp [fromCoefficients_apply, coeff_monomial, pairExponent_eq_iff, Fin.val_inj,
    ite_and]

theorem fromCoefficients_coeff_outside (c : PairIndex p → K) (e : Fin 2 →₀ ℕ)
    (he : p ≤ e 0 ∨ p ≤ e 1) : (fromCoefficients K p c).coeff e = 0 := by
  classical
  simp only [fromCoefficients_apply, coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hne : pairExponent i.val j.val ≠ e := by
    intro h
    have h0 := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
    have h1 := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
    simp only [pairExponent_zero, pairExponent_one] at h0 h1
    rcases he with he | he <;> omega
  simp [coeff_monomial, hne]

theorem fromCoefficients_mem (c : PairIndex p → K) :
    fromCoefficients K p c ∈ symmetricSpace K p := by
  refine ⟨fromCoefficients_coeff_outside c, ?_⟩
  intro i j
  rw [fromCoefficients_coeff, fromCoefficients_coeff, sortedPair_swap]

theorem fromCoefficients_injective : Function.Injective (fromCoefficients K p) := by
  intro c b h
  funext ij
  have hc := congrArg (fun f : Quartic.Poly K 2 =>
    f.coeff (pairExponent ij.val.1.val ij.val.2.val)) h
  rw [fromCoefficients_coeff, fromCoefficients_coeff,
    sortedPair_of_le ij.val.1 ij.val.2 ij.property] at hc
  exact hc

/-- Every polynomial in the bounded symmetric subspace is recovered from its
upper-triangular coefficient array. -/
theorem fromCoefficients_reconstruct (f : Quartic.Poly K 2) (hf : f ∈ symmetricSpace K p) :
    fromCoefficients K p (fun ij => f.coeff (pairExponent ij.val.1.val ij.val.2.val)) = f := by
  apply MvPolynomial.ext
  intro e
  by_cases h0 : e 0 < p
  · by_cases h1 : e 1 < p
    · let i : Fin p := ⟨e 0, h0⟩
      let j : Fin p := ⟨e 1, h1⟩
      have he : pairExponent i.val j.val = e := pairExponent_all e
      rw [← he, fromCoefficients_coeff]
      by_cases hij : i ≤ j
      · rw [sortedPair_of_le i j hij]
      · rw [sortedPair_swap i j, sortedPair_of_le j i (le_of_not_ge hij)]
        exact (hf.2 i j).symm
    · rw [fromCoefficients_coeff_outside _ e (Or.inr (by omega)), hf.1 e (Or.inr (by omega))]
  · rw [fromCoefficients_coeff_outside _ e (Or.inl (by omega)), hf.1 e (Or.inl (by omega))]

theorem range_fromCoefficients : LinearMap.range (fromCoefficients K p) = symmetricSpace K p := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    exact fromCoefficients_mem c
  · intro f hf
    exact ⟨_, fromCoefficients_reconstruct f hf⟩

instance symmetricSpaceFinite : Module.Finite K (symmetricSpace K p) := by
  rw [← range_fromCoefficients]
  infer_instance

theorem card_pairIndex : Fintype.card (PairIndex p) = (p + 1).choose 2 := by
  have h := Fintype.card_congr (Sym2.sortEquiv (α := Fin p))
  rw [Sym2.card] at h
  simpa using h.symm

/-- The dimension of the actual bounded symmetric bivariate polynomial space. -/
theorem symmetricSpace_finrank :
    Module.finrank K (symmetricSpace K p) = (p + 1).choose 2 := by
  rw [← range_fromCoefficients,
    LinearMap.finrank_range_of_inj (fromCoefficients_injective (K := K) (p := p))]
  simp [card_pairIndex]

/-- The variable interchange on bivariate polynomials. -/
def swapVariables : Equiv.Perm (Fin 2) := Equiv.swap 0 1

@[simp] theorem pairExponent_map_swap (a b : ℕ) :
    (pairExponent a b).mapDomain swapVariables = pairExponent b a := by
  simp [pairExponent, swapVariables, Finsupp.mapDomain_add, Finsupp.mapDomain_single, add_comm]

theorem fromCoefficients_symmetric (c : PairIndex p → K) :
    MvPolynomial.rename swapVariables (fromCoefficients K p c) = fromCoefficients K p c := by
  classical
  simp only [fromCoefficients_apply, map_sum, rename_monomial, pairExponent_map_swap]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [sortedPair_swap]

theorem symmetricSpace_rename (f : Quartic.Poly K 2) (hf : f ∈ symmetricSpace K p) :
    MvPolynomial.rename swapVariables f = f := by
  obtain ⟨c, rfl⟩ := range_fromCoefficients (K := K) (p := p) ▸ hf
  exact fromCoefficients_symmetric c

theorem symmetricSpace_degreeOf (hp : 1 ≤ p) (f : Quartic.Poly K 2)
    (hf : f ∈ symmetricSpace K p) (d : Fin 2) : f.degreeOf d ≤ p - 1 := by
  apply degreeOf_le_iff.mpr
  intro e he
  have hcoeff : f.coeff e ≠ 0 := mem_support_iff.mp he
  have hbound : e d < p := by
    by_contra h
    have hout : p ≤ e 0 ∨ p ≤ e 1 := by fin_cases d <;> simp_all
    exact hcoeff (hf.1 e hout)
  omega

/-- The coefficient definition agrees with the usual separate degree bound and
invariance under swapping the two variables. -/
theorem mem_symmetricSpace_iff (hp : 1 ≤ p) (f : Quartic.Poly K 2) :
    f ∈ symmetricSpace K p ↔
      (∀ d : Fin 2, f.degreeOf d ≤ p - 1) ∧ MvPolynomial.rename swapVariables f = f := by
  constructor
  · intro hf
    exact ⟨symmetricSpace_degreeOf hp f hf, symmetricSpace_rename f hf⟩
  · rintro ⟨hdeg, hsym⟩
    constructor
    · intro e he
      by_contra hcoeff
      have hes : e ∈ f.support := mem_support_iff.mpr hcoeff
      have h0 := (degreeOf_le_iff.mp (hdeg 0)) e hes
      have h1 := (degreeOf_le_iff.mp (hdeg 1)) e hes
      rcases he with he | he <;> omega
    · intro i j
      have h := coeff_rename_mapDomain swapVariables swapVariables.injective f
        (pairExponent i.val j.val)
      rw [hsym, pairExponent_map_swap] at h
      exact h.symm

/-- The degree bounds in the convolution parameter `t`. -/
theorem mem_convolution_factor_iff (t : ℕ) (ht : 2 ≤ t) (f : Quartic.Poly K 2) :
    f ∈ symmetricSpace K (t - 1) ↔
      (∀ d : Fin 2, f.degreeOf d ≤ t - 2) ∧ MvPolynomial.rename swapVariables f = f := by
  simpa [Nat.sub_sub] using mem_symmetricSpace_iff (K := K) (p := t - 1) (by omega) f

/-- The factor space required by the degree-two convolution inverse system. -/
theorem convolution_factor_finrank (t : ℕ) (ht : 2 ≤ t) :
    Module.finrank K (symmetricSpace K (t - 1)) = t.choose 2 := by
  rw [symmetricSpace_finrank]
  congr 1
  omega

end

end Quartic.ConvolutionSymmetric
