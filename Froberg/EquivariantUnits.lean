module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.MvPolynomial.Polynomial
public import Mathlib.Tactic

@[expose] public section

/-!
# Polynomial units and special-linear transvections

This file develops the regular-unit input of the equivariant divisibility
argument.  It does not assume divisibility of generic homology dimensions.
-/

namespace Froberg

open Polynomial Matrix

variable {K : Type*} [Field K] [Infinite K]

/-- Polynomial functions on the affine line which are mutual multiplicative
inverses are constant.  The hypothesis is pointwise, so this applies directly
to restrictions of regular units to polynomial one-parameter families. -/
theorem polynomial_unit_function_constant
    (P Q : Polynomial K) (hinv : ∀ t : K, P.eval t * Q.eval t = 1) (t : K) :
    P.eval t = P.eval 0 := by
  have hPQ : P * Q = 1 := by
    apply Polynomial.funext
    intro x
    simpa only [Polynomial.eval_mul, Polynomial.eval_one] using hinv x
  have hunit : IsUnit P := isUnit_iff_dvd_one.mpr ⟨Q, hPQ.symm⟩
  have hdeg : P.degree = 0 := Polynomial.isUnit_iff_degree_eq_zero.mp hunit
  rw [Polynomial.eq_C_of_degree_eq_zero hdeg]
  simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluate a coordinate polynomial on the entries of a special-linear
matrix.  The polynomial is permitted to have any degree. -/
noncomputable def slPolynomialEval
    (P : MvPolynomial (ι × ι) K) (g : Matrix.SpecialLinearGroup ι K) : K :=
  MvPolynomial.eval (fun ij => g ij.1 ij.2) P

omit [Infinite K] in
/-- A coordinate polynomial restricted to a right transvection coset is a
univariate polynomial function. -/
theorem slPolynomialEval_transvection_polynomial
    (P : MvPolynomial (ι × ι) K) (g : Matrix.SpecialLinearGroup ι K)
    (i j : ι) (hij : i ≠ j) :
    ∃ R : Polynomial K, ∀ t : K,
      R.eval t = slPolynomialEval P (g * Matrix.SpecialLinearGroup.transvection hij t) := by
  let entry : ι × ι → Polynomial K := fun kl =>
    C (g kl.1 kl.2) + if kl.2 = j then X * C (g kl.1 i) else 0
  refine ⟨MvPolynomial.eval₂Hom Polynomial.C entry P, ?_⟩
  intro t
  change (Polynomial.evalRingHom t) (MvPolynomial.eval₂Hom Polynomial.C entry P) = _
  rw [MvPolynomial.map_eval₂Hom]
  have hcoeff : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id K := by
    ext x
    simp
  rw [hcoeff]
  change MvPolynomial.eval (fun kl => (Polynomial.evalRingHom t) (entry kl)) P = _
  unfold slPolynomialEval
  apply congrArg (fun f : ι × ι → K => MvPolynomial.eval f P)
  funext kl
  rcases kl with ⟨k, l⟩
  by_cases hl : l = j
  · subst l
    simp [entry, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_add]
  · simp [entry, hl, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_add]

/-- A polynomial regular unit on `SL` is invariant under right multiplication
by every transvection.  This proves the one-parameter invariance step of the
manuscript's regular-unit argument. -/
theorem slPolynomialUnit_right_transvection
    (P Q : MvPolynomial (ι × ι) K)
    (hinv : ∀ g : Matrix.SpecialLinearGroup ι K,
      slPolynomialEval P g * slPolynomialEval Q g = 1)
    (g : Matrix.SpecialLinearGroup ι K) (i j : ι) (hij : i ≠ j) (t : K) :
    slPolynomialEval P (g * Matrix.SpecialLinearGroup.transvection hij t) =
      slPolynomialEval P g := by
  obtain ⟨R, hR⟩ := slPolynomialEval_transvection_polynomial P g i j hij
  obtain ⟨S, hS⟩ := slPolynomialEval_transvection_polynomial Q g i j hij
  have hRS : ∀ x : K, R.eval x * S.eval x = 1 := by
    intro x
    rw [hR, hS]
    exact hinv _
  have hconst := polynomial_unit_function_constant R S hRS t
  rw [hR, hR] at hconst
  simpa only [Matrix.SpecialLinearGroup.transvection_coeff_zero, mul_one] using hconst

omit [Infinite K] in
/-- A two-coordinate diagonal matrix is explicitly a product of six
transvections, in arbitrary matrix size. -/
theorem sl_diag2n_decompose (i j : ι) (hij : i ≠ j) (a : K) (ha : a ≠ 0) :
    Matrix.SpecialLinearGroup.diag2n hij a ha =
      Matrix.SpecialLinearGroup.transvection hij a *
      Matrix.SpecialLinearGroup.transvection hij.symm (-a⁻¹) *
      Matrix.SpecialLinearGroup.transvection hij a *
      Matrix.SpecialLinearGroup.transvection hij (-1) *
      Matrix.SpecialLinearGroup.transvection hij.symm 1 *
      Matrix.SpecialLinearGroup.transvection hij (-1) := by
  ext k l
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
    subst_vars <;> try contradiction
  all_goals
    simp_all [Matrix.SpecialLinearGroup.diag2n_coe,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.diagonal_apply, Matrix.one_apply,
      Matrix.mul_add, Matrix.add_mul, eq_comm]

/-- A polynomial function on `SL` with a polynomial reciprocal is constant.
This is the algebraic regular-unit theorem used in the determinant-line proof
of equivariant divisibility. -/
theorem slPolynomialUnit_constant
    (P Q : MvPolynomial (ι × ι) K)
    (hinv : ∀ g : Matrix.SpecialLinearGroup ι K,
      slPolynomialEval P g * slPolynomialEval Q g = 1)
    (g : Matrix.SpecialLinearGroup ι K) :
    slPolynomialEval P g = slPolynomialEval P 1 := by
  rcases subsingleton_or_nontrivial ι with hsub | hnontriv
  · have := hsub
    congr 1
    exact Subsingleton.elim g 1
  · have := hnontriv
    let Invariant : Matrix.SpecialLinearGroup ι K → Prop := fun a =>
      ∀ b, slPolynomialEval P (b * a) = slPolynomialEval P b
    have hmul : ∀ a b, Invariant a → Invariant b → Invariant (a * b) := by
      intro a b ha hb c
      rw [← mul_assoc, hb, ha]
    have htrans : ∀ (i j : ι) (hij : i ≠ j) (a : K),
        Invariant (Matrix.SpecialLinearGroup.transvection hij a) := by
      intro i j hij a b
      exact slPolynomialUnit_right_transvection P Q hinv b i j hij a
    have hdiag : ∀ (i j : ι) (hij : i ≠ j) (a : K) (ha : a ≠ 0),
        Invariant (Matrix.SpecialLinearGroup.diag2n hij a ha) := by
      intro i j hij a ha
      rw [sl_diag2n_decompose i j hij a ha]
      exact hmul _ _
        (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _
          (htrans i j hij a) (htrans j i hij.symm (-a⁻¹)))
          (htrans i j hij a)) (htrans i j hij (-1)))
          (htrans j i hij.symm 1)) (htrans i j hij (-1))
    have hg : Invariant g :=
      Matrix.SpecialLinearGroup.diagonal_transvection_induction' Invariant g
        (fun i j hij _ ha => hdiag i j hij _ ha) htrans hmul
    simpa only [one_mul] using hg 1

end Froberg
