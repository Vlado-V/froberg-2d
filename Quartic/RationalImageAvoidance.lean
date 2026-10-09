module

public import Quartic.PolynomialImageAvoidance
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Algebraic.Basic

@[expose] public section

/-!
# Avoiding lower-dimensional rational charts

A rational chart with a common polynomial denominator is evaluated only where
that denominator is nonzero. Localization supplies a polynomial relation on
the whole chart. Finite unions of such charts are contained in a proper
polynomial zero set over an infinite field.
-/
noncomputable section
namespace Quartic.RationalImageAvoidance
open MvPolynomial PolynomialImageAvoidance
variable {K I J : Type*} [Field K]

abbrev AwayRing (G : MvPolynomial I K) := Localization.Away G

/-- A rational coordinate tuple in the localization at its common denominator. -/
def localizedCoordinates (F : J → MvPolynomial I K) (G : MvPolynomial I K) :
    J → AwayRing G :=
  fun j => algebraMap (MvPolynomial I K) (AwayRing G) (F j) * IsLocalization.Away.invSelf G

/-- The actual rational map on the principal open where its denominator is nonzero. -/
def rationalMap (F : J → MvPolynomial I K) (G : MvPolynomial I K) (a : I → K) : J → K :=
  fun j => eval a (F j) / eval a G

/-- Localization at a nonzero denominator does not add transcendence degree. -/
theorem trdeg_away (G : MvPolynomial I K) (hG : G ≠ 0) :
    Algebra.trdeg K (AwayRing G) = Algebra.trdeg K (MvPolynomial I K) := by
  let : IsDomain (AwayRing G) := Localization.Away.isDomain hG
  let : FaithfulSMul (MvPolynomial I K) (AwayRing G) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (IsLocalization.injective (AwayRing G) (powers_le_nonZeroDivisors_of_noZeroDivisors hG))
  let : Algebra.IsAlgebraic (MvPolynomial I K) (AwayRing G) :=
    IsLocalization.isAlgebraic (AwayRing G) (Submonoid.powers G)
  have h := trdeg_add_eq K (MvPolynomial I K) (A := AwayRing G)
  have hz : Algebra.trdeg (MvPolynomial I K) (AwayRing G) = 0 :=
    trdeg_eq_zero_iff.mpr inferInstance
  rw [hz, add_zero] at h
  exact h.symm

/-- The rational coordinates satisfy a nonzero polynomial relation whenever
there are more output coordinates than parameters. -/
theorem exists_localized_annihilator [Fintype I] [Fintype J]
    (F : J → MvPolynomial I K) (G : MvPolynomial I K) (hG : G ≠ 0)
    (hcard : Fintype.card I < Fintype.card J) :
    ∃ P : MvPolynomial J K, P ≠ 0 ∧ aeval (localizedCoordinates F G) P = 0 := by
  classical
  let : IsDomain (AwayRing G) := Localization.Away.isDomain hG
  by_contra h
  have hF : AlgebraicIndependent K (localizedCoordinates F G) := by
    rw [algebraicIndependent_iff]
    intro P hP
    by_contra hP0
    exact h ⟨P, hP0, hP⟩
  have hr := hF.lift_cardinalMk_le_trdeg
  rw [trdeg_away G hG] at hr
  simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, Cardinal.lift_natCast] at hr
  have hc : Fintype.card J ≤ Fintype.card I := by exact_mod_cast hr
  omega

/-- Evaluation is a well-defined algebra map on the relevant localization. -/
def evaluateAway (G : MvPolynomial I K) (a : I → K) (ha : eval a G ≠ 0) :
    AwayRing G →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom G (f := aeval a) (isUnit_iff_ne_zero.mpr ha)

@[simp] theorem evaluateAway_algebraMap (G : MvPolynomial I K) (a : I → K)
    (ha : eval a G ≠ 0) (F : MvPolynomial I K) :
    evaluateAway G a ha (algebraMap (MvPolynomial I K) (AwayRing G) F) = eval a F := by
  simp [evaluateAway]

theorem evaluateAway_inverse (G : MvPolynomial I K) (a : I → K) (ha : eval a G ≠ 0) :
    evaluateAway G a ha (IsLocalization.Away.invSelf G) = (eval a G)⁻¹ := by
  have h := congrArg (evaluateAway G a ha) (IsLocalization.Away.mul_invSelf (S := AwayRing G) G)
  simp only [map_mul, evaluateAway_algebraMap, map_one] at h
  apply mul_left_cancel₀ ha
  rw [h, mul_inv_cancel₀ ha]

/-- The localization relation vanishes at every point of the rational chart's domain. -/
theorem eval_rationalMap (F : J → MvPolynomial I K) (G : MvPolynomial I K)
    (a : I → K) (ha : eval a G ≠ 0) (P : MvPolynomial J K) :
    eval (rationalMap F G a) P = evaluateAway G a ha (aeval (localizedCoordinates F G) P) := by
  have hc : (fun j => evaluateAway G a ha (localizedCoordinates F G j)) = rationalMap F G a := by
    funext j
    simp [localizedCoordinates, rationalMap, evaluateAway_inverse, div_eq_mul_inv]
  have h := comp_aeval_apply (f := localizedCoordinates F G) (evaluateAway G a ha) P
  rw [hc] at h
  exact h.symm

/-- A rational image of lower parameter dimension is contained in a nonzero
polynomial zero set. A zero denominator simply gives the empty domain. -/
theorem exists_equation_for_rational_image [Fintype I] [Fintype J]
    (F : J → MvPolynomial I K) (G : MvPolynomial I K)
    (hcard : Fintype.card I < Fintype.card J) :
    ∃ P : MvPolynomial J K, P ≠ 0 ∧
      ∀ a : I → K, eval a G ≠ 0 → eval (rationalMap F G a) P = 0 := by
  by_cases hG : G = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    intro a ha
    simp [hG] at ha
  obtain ⟨P, hP, hF⟩ := exists_localized_annihilator F G hG hcard
  exact ⟨P, hP, fun a ha => by rw [eval_rationalMap F G a ha, hF, map_zero]⟩

section FiniteCharts
variable {C : Type*} [Fintype C] (Param : C → Type*) [∀ c, Fintype (Param c)] [Fintype J]

/-- A finite union of lower-dimensional rational charts has a common nonzero
polynomial equation on all of their actual domains. -/
theorem exists_equation_for_finite_union
    (F : (c : C) → J → MvPolynomial (Param c) K)
    (G : (c : C) → MvPolynomial (Param c) K)
    (hcard : ∀ c, Fintype.card (Param c) < Fintype.card J) :
    ∃ P : MvPolynomial J K, P ≠ 0 ∧
      ∀ c a, eval a (G c) ≠ 0 → eval (rationalMap (F c) (G c) a) P = 0 := by
  classical
  choose P hP hF using fun c => exists_equation_for_rational_image (F c) (G c) (hcard c)
  refine ⟨∏ c, P c, Finset.prod_ne_zero_iff.mpr (fun c _ => hP c), ?_⟩
  intro c a ha
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ c) (hF c a ha)

/-- A nonempty principal open simultaneously avoids every lower-dimensional
rational chart in a finite family, over any infinite field. -/
theorem principal_open_avoids_finite_union [Infinite K]
    (F : (c : C) → J → MvPolynomial (Param c) K)
    (G : (c : C) → MvPolynomial (Param c) K)
    (hcard : ∀ c, Fintype.card (Param c) < Fintype.card J) :
    ∃ P : MvPolynomial J K, (∃ x : J → K, eval x P ≠ 0) ∧
      ∀ x, eval x P ≠ 0 → ∀ c a, eval a (G c) ≠ 0 → x ≠ rationalMap (F c) (G c) a := by
  obtain ⟨P, hP, hF⟩ := exists_equation_for_finite_union Param F G hcard
  refine ⟨P, exists_eval_ne_zero hP, ?_⟩
  intro x hx c a ha hxa
  rw [hxa] at hx
  exact hx (hF c a ha)

/-- A target point outside all charts follows from the proved proper equation. -/
theorem exists_outside_finite_union [Infinite K]
    (F : (c : C) → J → MvPolynomial (Param c) K)
    (G : (c : C) → MvPolynomial (Param c) K)
    (hcard : ∀ c, Fintype.card (Param c) < Fintype.card J) :
    ∃ x : J → K, ∀ c a, eval a (G c) ≠ 0 → x ≠ rationalMap (F c) (G c) a := by
  obtain ⟨P, ⟨x, hx⟩, h⟩ := principal_open_avoids_finite_union Param F G hcard
  exact ⟨x, h x hx⟩

end FiniteCharts

end Quartic.RationalImageAvoidance
