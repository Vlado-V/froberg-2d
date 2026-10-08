import Quartic.RankOpen
import Quartic.RationalCurve

/-!
# Polynomial parameter curves and rank

A rank attained at one parameter is a lower bound outside finitely many
parameters. The proof substitutes the parameter polynomials in a determinant
neighborhood and uses finiteness of the roots of a nonzero polynomial.
-/

noncomputable section

namespace Quartic.PolynomialRank

open Module Filter Polynomial

variable {K V W ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
  [Fintype ι] [DecidableEq ι]

theorem rank_eventually_ge (A : (ι → K) →ₗ[K] (V →ₗ[K] W))
    (γ : ι → K[X]) (t₀ : K) :
    ∀ᶠ t in cofinite,
      finrank K (LinearMap.range (A (fun i => (γ i).eval t₀))) ≤
        finrank K (LinearMap.range (A (fun i => (γ i).eval t))) := by
  obtain ⟨D, hD, hrank⟩ := rank_principal_open A (fun i => (γ i).eval t₀)
  let P : K[X] := MvPolynomial.eval₂Hom Polynomial.C γ D
  have heval (t : K) : P.eval t = MvPolynomial.eval (fun i => (γ i).eval t) D := by
    change (Polynomial.evalRingHom t) (MvPolynomial.eval₂Hom Polynomial.C γ D) = _
    rw [MvPolynomial.map_eval₂Hom]
    congr 2
    ext c
    simp
  have hP : P ≠ 0 := by
    intro hz
    apply hD
    rw [← heval t₀, hz]
    exact Polynomial.eval_zero
  filter_upwards [Polynomial.eventually_eval_ne_zero_cofinite hP] with t ht
  exact hrank _ (by rwa [heval] at ht)

end Quartic.PolynomialRank
