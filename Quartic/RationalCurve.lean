import Quartic.SymmetricEvaluation

/-!
# Symmetric evaluation on a rational normal curve

The affine parameter `(1,t,...,t^(p-1))` is the evaluation vector for binary
forms of degree `p-1` on the affine chart. A nonzero linear functional on this
curve is a nonzero polynomial, so it has only finitely many zeros. This verifies
the genericity hypothesis of the symmetric evaluation bound in the case used
by the convolution module.
-/

noncomputable section

namespace Quartic.RationalCurve

open Module Filter Polynomial

variable {K : Type*} [Field K] (p : ℕ)

def point (t : K) : Fin p → K := fun i => t ^ i.val

def functionalPolynomial (L : (Fin p → K) →ₗ[K] K) : K[X] :=
  ∑ i : Fin p, C (L (Pi.single i 1)) * X ^ i.val

theorem eval_functionalPolynomial (L : (Fin p → K) →ₗ[K] K) (t : K) :
    (functionalPolynomial p L).eval t = L (point p t) := by
  classical
  have h := congrArg L ((Pi.basisFun K (Fin p)).sum_equivFun (point p t))
  simp only [functionalPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  simpa only [point, map_sum, map_smul, Pi.basisFun_apply,
    Pi.basisFun_equivFun, LinearEquiv.refl_apply, smul_eq_mul, mul_comm] using h

theorem coeff_functionalPolynomial (L : (Fin p → K) →ₗ[K] K) (i : Fin p) :
    (functionalPolynomial p L).coeff i.val = L (Pi.single i 1) := by
  classical
  simp only [functionalPolynomial, finsetSum_coeff, coeff_C_mul_X_pow]
  have heq (j : Fin p) : i.val = j.val ↔ i = j := Fin.val_inj
  simp [heq]

theorem functionalPolynomial_ne_zero (L : (Fin p → K) →ₗ[K] K) (hL : L ≠ 0) :
    functionalPolynomial p L ≠ 0 := by
  intro hzero
  have hcoeff (i : Fin p) : L (Pi.single i 1) = 0 := by
    rw [← coeff_functionalPolynomial p L i, hzero]
    exact coeff_zero _
  apply hL
  apply LinearMap.ext
  intro a
  have h := congrArg L ((Pi.basisFun K (Fin p)).sum_equivFun a)
  simpa [map_sum, Pi.basisFun_apply, hcoeff] using h.symm

theorem curve_avoids_hyperplanes :
    SymmetricEvaluation.AvoidsHyperplanes (K := K) (Filter.map (point (K := K) p) cofinite) := by
  intro L hL
  change ∀ᶠ t in cofinite, L (point p t) ≠ 0
  simpa only [eval_functionalPolynomial] using
    Polynomial.eventually_eval_ne_zero_cofinite (functionalPolynomial_ne_zero p L hL)

/-- The manuscript's binomial bound for symmetric forms evaluated on binary
evaluation vectors. The rank bound may fail at finitely many parameters. -/
theorem symmetric_dimension_bound [Infinite K]
    {U : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (H : U →ₗ[K] ((Fin p → K) →ₗ[K] (Fin p → K) →ₗ[K] K))
    (hH : Function.Injective H)
    (hsym : ∀ u x y, H u x y = H u y x) (b : ℕ)
    (hrank : ∀ᶠ t in cofinite,
      finrank K (LinearMap.range (SymmetricEvaluation.evaluation H (point p t))) ≤ b) :
    finrank K U ≤ (b + 1).choose 2 :=
  SymmetricEvaluation.dimension_bound (Filter.map (point p) cofinite)
    (curve_avoids_hyperplanes p) b H hH hsym hrank

end Quartic.RationalCurve
