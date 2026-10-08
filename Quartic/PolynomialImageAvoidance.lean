import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

/-!
# Avoiding polynomial images of smaller parameter dimension

A polynomial map from fewer parameters than target coordinates satisfies a
nonzero polynomial equation. Over an infinite field its image, and any finite
union of such images, is contained in a proper polynomial zero set. This is an
affine polynomial-chart statement; it asserts no incidence-variety or
Grassmannian chart construction.
-/
noncomputable section
namespace Quartic.PolynomialImageAvoidance
open MvPolynomial
variable {K I J : Type*} [Field K]

/-- Evaluation of a tuple of coordinate polynomials. -/
def polynomialMap (F : J → MvPolynomial I K) (a : I → K) : J → K :=
  fun j => eval a (F j)

/-- Transcendence degree bounds the number of algebraically independent
polynomials by the number of parameter variables. -/
theorem card_le_of_algebraicIndependent [Fintype I] [Fintype J]
    (F : J → MvPolynomial I K) (hF : AlgebraicIndependent K F) :
    Fintype.card J ≤ Fintype.card I := by
  have h := hF.lift_cardinalMk_le_trdeg
  simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype,
    Cardinal.lift_natCast] at h
  exact_mod_cast h

/-- A polynomial tuple with more coordinates than parameters has a nonzero
polynomial relation. Algebraic dependence is proved from the dimension bound. -/
theorem exists_annihilator_of_card_lt [Fintype I] [Fintype J]
    (F : J → MvPolynomial I K) (hcard : Fintype.card I < Fintype.card J) :
    ∃ P : MvPolynomial J K, P ≠ 0 ∧ aeval F P = 0 := by
  classical
  by_contra h
  have hF : AlgebraicIndependent K F := by
    rw [algebraicIndependent_iff]
    intro P hP
    by_contra hP0
    exact h ⟨P, hP0, hP⟩
  exact (Nat.not_le_of_lt hcard) (card_le_of_algebraicIndependent F hF)

/-- Polynomial substitution agrees with evaluation along the polynomial map. -/
theorem eval_polynomialMap (F : J → MvPolynomial I K) (a : I → K)
    (P : MvPolynomial J K) :
    eval (polynomialMap F a) P = eval a (aeval F P) := by
  change aeval (fun j => aeval a (F j)) P = aeval a (aeval F P)
  exact (comp_aeval_apply (f := F) (aeval a) P).symm

/-- Every nonzero polynomial over an infinite field is nonzero at some point. -/
theorem exists_eval_ne_zero [Infinite K] {P : MvPolynomial J K} (hP : P ≠ 0) :
    ∃ x : J → K, eval x P ≠ 0 := by
  by_contra h
  apply hP
  apply MvPolynomial.funext
  intro x
  have hx : eval x P = 0 := by simpa using not_exists.mp h x
  simpa using hx

/-- A lower-dimensional polynomial chart is contained in the zero set of a
nonzero polynomial, as a statement about actual evaluated points. -/
theorem exists_equation_for_image [Fintype I] [Fintype J]
    (F : J → MvPolynomial I K) (hcard : Fintype.card I < Fintype.card J) :
    ∃ P : MvPolynomial J K, P ≠ 0 ∧
      ∀ a : I → K, eval (polynomialMap F a) P = 0 := by
  obtain ⟨P, hP, hF⟩ := exists_annihilator_of_card_lt F hcard
  exact ⟨P, hP, fun a => by rw [eval_polynomialMap, hF, map_zero]⟩

/-- The image of a lower-dimensional polynomial chart omits a target point
over every infinite field. -/
theorem exists_outside_image [Infinite K] [Fintype I] [Fintype J]
    (F : J → MvPolynomial I K) (hcard : Fintype.card I < Fintype.card J) :
    ∃ x : J → K, x ∉ Set.range (polynomialMap F) := by
  obtain ⟨P, hP, hF⟩ := exists_equation_for_image F hcard
  obtain ⟨x, hx⟩ := exists_eval_ne_zero hP
  refine ⟨x, ?_⟩
  rintro ⟨a, rfl⟩
  exact hx (hF a)

section FiniteCharts
variable {C : Type*} [Fintype C] (Param : C → Type*) [∀ c, Fintype (Param c)]
variable [Fintype J]

/-- A finite family of lower-dimensional polynomial charts has one common
nonzero annihilator, obtained by multiplying their individual relations. -/
theorem exists_common_annihilator
    (F : (c : C) → J → MvPolynomial (Param c) K)
    (hcard : ∀ c, Fintype.card (Param c) < Fintype.card J) :
    ∃ P : MvPolynomial J K, P ≠ 0 ∧ ∀ c, aeval (F c) P = 0 := by
  classical
  choose P hP hF using fun c => exists_annihilator_of_card_lt (F c) (hcard c)
  refine ⟨∏ c, P c, Finset.prod_ne_zero_iff.mpr (fun c _ => hP c), ?_⟩
  intro c
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ c) (hF c)

/-- A finite union of polynomial charts with fewer parameters than target
coordinates lies in a proper polynomial zero set over an infinite field. -/
theorem exists_proper_equation_for_finite_union [Infinite K]
    (F : (c : C) → J → MvPolynomial (Param c) K)
    (hcard : ∀ c, Fintype.card (Param c) < Fintype.card J) :
    ∃ P : MvPolynomial J K, P ≠ 0 ∧
      (∀ c a, eval (polynomialMap (F c) a) P = 0) ∧
      ∃ x : J → K, eval x P ≠ 0 := by
  obtain ⟨P, hP, hF⟩ := exists_common_annihilator Param F hcard
  refine ⟨P, hP, ?_, exists_eval_ne_zero hP⟩
  intro c a
  rw [eval_polynomialMap, hF c, map_zero]

/-- A target point simultaneously avoids all charts in the finite family. -/
theorem exists_outside_finite_union [Infinite K]
    (F : (c : C) → J → MvPolynomial (Param c) K)
    (hcard : ∀ c, Fintype.card (Param c) < Fintype.card J) :
    ∃ x : J → K, ∀ c, x ∉ Set.range (polynomialMap (F c)) := by
  obtain ⟨P, _, hF, x, hx⟩ := exists_proper_equation_for_finite_union Param F hcard
  refine ⟨x, ?_⟩
  rintro c ⟨a, rfl⟩
  exact hx (hF c a)

end FiniteCharts
end Quartic.PolynomialImageAvoidance
