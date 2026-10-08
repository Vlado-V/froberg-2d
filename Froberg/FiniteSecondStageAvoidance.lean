import Quartic.FiniteAlgebraicKernelAvoidance
import Froberg.SecondStageAvoidance

/-! A finite-module slice certificate gives an open set of second-stage
parameters which works for every first-stage kernel vector. -/
noncomputable section
universe u
namespace Quartic.FiniteAlgebraicKernelAvoidance
open MvPolynomial Matrix Algebra KernelPolynomialCharts
variable {K R : Type u} [Field K] [CommRing R] [Algebra K R]
variable {I : Type} {a b n l r s g : ℕ}

/-- Module-finite slice coordinates supply every component dimension bound
needed by the algebraic two-stage chart argument. -/
theorem equation_second_stage
    (slices : Fin g → R)
    [Module.Finite (Algebra.adjoin K (Set.range slices)) R]
    (base : I → R)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (B : Matrix (Fin b) (Fin l) (MvPolynomial (I ⊕ Fin n) K))
    (hcount : g+n < r+s) :
    ∃ P : MvPolynomial (Fin l) K, P ≠ 0 ∧
      ∀ (φ : R →ₐ[K] K) (x : Fin n → K) (y : Fin l → K),
        r ≤ (evaluated A (fun i => φ (base i))).rank →
        s ≤ (evaluated B (Sum.elim (fun i => φ (base i)) x)).rank →
        evaluated A (fun i => φ (base i)) *ᵥ x = 0 →
        evaluated B (Sum.elim (fun i => φ (base i)) x) *ᵥ y = 0 →
        eval y P = 0 := by
  let : Algebra.FiniteType K R :=
    AlgebraicDomainDimension.finiteType_of_finite_adjoin (K := K) slices
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  apply AlgebraicKernelAvoidance.equation_second_stage_components base _ A B hcount
  intro p hp
  let : p.IsPrime := hp.isPrime
  exact AlgebraicDomainDimension.trdeg_prime_quotient_le slices p

/-- Only the second-stage parameters are selected; the first constrained
vector and every base point remain universally quantified. -/
theorem principal_open_second_stage [Infinite K]
    (slices : Fin g → R)
    [Module.Finite (Algebra.adjoin K (Set.range slices)) R]
    (base : I → R)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (B : Matrix (Fin b) (Fin l) (MvPolynomial (I ⊕ Fin n) K))
    (hcount : g+n < r+s) :
    ∃ P : MvPolynomial (Fin l) K,
      (∃ y : Fin l → K, eval y P ≠ 0) ∧
      ∀ y, eval y P ≠ 0 → ∀ (φ : R →ₐ[K] K) (x : Fin n → K),
        let t := fun i => φ (base i)
        r ≤ (evaluated A t).rank →
        s ≤ (evaluated B (Sum.elim t x)).rank →
        evaluated A t *ᵥ x ≠ 0 ∨ evaluated B (Sum.elim t x) *ᵥ y ≠ 0 := by
  let : Algebra.FiniteType K R :=
    AlgebraicDomainDimension.finiteType_of_finite_adjoin (K := K) slices
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  apply AlgebraicKernelAvoidance.principal_open_second_stage base _ A B hcount
  intro p hp
  let : p.IsPrime := hp.isPrime
  exact AlgebraicDomainDimension.trdeg_prime_quotient_le slices p

end Quartic.FiniteAlgebraicKernelAvoidance
