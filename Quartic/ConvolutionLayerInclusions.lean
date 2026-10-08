import Quartic.FreeCoefficientProducts

/-!
# Actual insertion maps in the grouped convolution layers

Free-monomial multiplication gives exactly the coordinate inclusions in the
degree-one and degree-three decompositions. These identities connect the
polynomial multiplication maps with the subspaces counted in each layer.
-/

noncomputable section
namespace Quartic.ConvolutionLayerInclusions
open FreeCoefficients FreeMonomialCounts ConvolutionFreePieces ConvolutionFreeMultiplication
open ConvolutionLayers FreeCoefficientProducts
variable {K : Type*} [Field K] {t w d k l : ℕ}

theorem exponent_ne_of_degree_ne (b : ExactExponent w k) (e : ExactExponent w l)
    (h : k ≠ l) : b.val ≠ e.val := by
  intro he
  have hd := congrArg Finsupp.degree he
  exact h (b.property.symm.trans (hd.trans e.property))

/-- Off-diagonal coefficient extraction vanishes before taking the quotient. -/
theorem coefficientRows_insert_ne (b : ExactExponent w k) (e : ExactExponent w l)
    (hne : b.val ≠ e.val) (v : ConvolutionFree.Target K t 0 d) :
    coefficientRows e (targetCast (congrArg (d + ·) b.property) (rowLift b.val v)) = 0 := by
  funext r
  apply Subtype.ext
  simp [coefficientRows, freeCoeff_liftCoeff, hne]

/-- The diagonal coefficient extraction recovers the original core rows. -/
theorem coefficientRows_insert_self (b : ExactExponent w k) (v : ConvolutionFree.Target K t 0 d) :
    coefficientRows b (targetCast (congrArg (d + ·) b.property) (rowLift b.val v)) =
      targetCast (Nat.add_sub_cancel d k).symm v := by
  funext r
  apply Subtype.ext
  simp [coefficientRows, freeCoeff_liftCoeff]

/-- The embedded first core piece is the first coordinate of `N₁`. -/
theorem degreeOne_insert_core (x : Piece K t 0 1) :
    degreeOneEquiv (insertAt (zeroExponent w) x) = (x, 0) := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  rw [insertAt_mk]
  apply Prod.ext
  · rw [degreeOneEquiv_mk_core, coefficientRows_insert_self]
    rfl
  · funext i
    rw [degreeOneEquiv_mk_free,
      coefficientRows_insert_ne _ _ (exponent_ne_of_degree_ne _ _ (by decide : 0 ≠ 1))]
    rfl

/-- Multiplication of an output class by one free variable is its single free coordinate. -/
theorem degreeOne_insert_free (i : Fin w) (x : Piece K t 0 0) :
    degreeOneEquiv (insertAt (oneExponentEquiv i) x) = (0, Pi.single i x) := by
  classical
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  rw [insertAt_mk]
  apply Prod.ext
  · rw [degreeOneEquiv_mk_core,
      coefficientRows_insert_ne _ _ (exponent_ne_of_degree_ne _ _ (by decide : 1 ≠ 0))]
    rfl
  · funext j
    rw [degreeOneEquiv_mk_free]
    by_cases hij : i = j
    · subst j
      rw [coefficientRows_insert_self]
      simp
    · have hne : (oneExponentEquiv i).val ≠ (oneExponentEquiv j).val := by
        intro h
        exact hij (oneExponentEquiv.injective (Subtype.ext h))
      rw [coefficientRows_insert_ne _ _ hne]
      simp [hij]

/-- Core quadratics times a free variable occupy exactly the first cubic layer. -/
theorem degreeThree_insert_linear (i : Fin w) (x : Piece K t 0 2) :
    degreeThreeEquiv (insertAt (oneExponentEquiv i) x) = (Pi.single i x, 0, 0) := by
  classical
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  rw [insertAt_mk]
  apply Prod.ext
  · funext j
    rw [degreeThreeEquiv_mk_linear]
    by_cases hij : i = j
    · subst j
      rw [coefficientRows_insert_self]
      simp
    · have hne : (oneExponentEquiv i).val ≠ (oneExponentEquiv j).val := by
        intro h
        exact hij (oneExponentEquiv.injective (Subtype.ext h))
      rw [coefficientRows_insert_ne _ _ hne]
      simp [hij]
  · apply Prod.ext
    · funext b
      rw [degreeThreeEquiv_mk_quadratic,
        coefficientRows_insert_ne _ _ (exponent_ne_of_degree_ne _ _ (by decide : 1 ≠ 2))]
      rfl
    · funext b
      rw [degreeThreeEquiv_mk_cubic,
        coefficientRows_insert_ne _ _ (exponent_ne_of_degree_ne _ _ (by decide : 1 ≠ 3))]
      rfl

/-- Core linear classes times a free quadratic occupy exactly the second cubic layer. -/
theorem degreeThree_insert_quadratic (b : ExactExponent w 2) (x : Piece K t 0 1) :
    degreeThreeEquiv (insertAt b x) = (0, Pi.single b x, 0) := by
  classical
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  rw [insertAt_mk]
  apply Prod.ext
  · funext i
    rw [degreeThreeEquiv_mk_linear,
      coefficientRows_insert_ne _ _ (exponent_ne_of_degree_ne _ _ (by decide : 2 ≠ 1))]
    rfl
  · apply Prod.ext
    · funext e
      rw [degreeThreeEquiv_mk_quadratic]
      by_cases hbe : b = e
      · subst e
        rw [coefficientRows_insert_self]
        simp
      · rw [coefficientRows_insert_ne _ _ (fun h => hbe (Subtype.ext h))]
        simp [hbe]
    · funext e
      rw [degreeThreeEquiv_mk_cubic,
        coefficientRows_insert_ne _ _ (exponent_ne_of_degree_ne _ _ (by decide : 2 ≠ 3))]
      rfl

/-- Output classes times free cubics occupy exactly the final cubic layer. -/
theorem degreeThree_insert_cubic (b : ExactExponent w 3) (x : Piece K t 0 0) :
    degreeThreeEquiv (insertAt b x) = (0, 0, Pi.single b x) := by
  classical
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  rw [insertAt_mk]
  apply Prod.ext
  · funext i
    rw [degreeThreeEquiv_mk_linear,
      coefficientRows_insert_ne _ _ (exponent_ne_of_degree_ne _ _ (by decide : 3 ≠ 1))]
    rfl
  · apply Prod.ext
    · funext e
      rw [degreeThreeEquiv_mk_quadratic,
        coefficientRows_insert_ne _ _ (exponent_ne_of_degree_ne _ _ (by decide : 3 ≠ 2))]
      rfl
    · funext e
      rw [degreeThreeEquiv_mk_cubic]
      by_cases hbe : b = e
      · subst e
        rw [coefficientRows_insert_self]
        simp
      · rw [coefficientRows_insert_ne _ _ (fun h => hbe (Subtype.ext h))]
        simp [hbe]

end Quartic.ConvolutionLayerInclusions
