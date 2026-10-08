import Quartic.AlgebraicDomainDimension
import Quartic.AlgebraicKernelAvoidance

/-!
# Avoidance from an actual finite-module slice certificate

A coordinate algebra finite as a module over `g` specified slice elements
has finitely many components, each of transcendence degree at most `g`.
Consequently two successive linear kernel conditions of ranks at least
`r` and `s` admit a nonempty avoiding motion open when `g < r+s`.
Neither rationality, reducedness, Noetherianity, nor a dimension bound is
assumed of the coordinate algebra.
-/
noncomputable section
universe u
namespace Quartic.FiniteAlgebraicKernelAvoidance
open MvPolynomial Matrix Algebra KernelPolynomialCharts
variable {K R : Type u} [Field K] [CommRing R] [Algebra K R]
variable {I : Type} {a b n l r s g : ℕ}

/-- Module-finite slice coordinates supply every component dimension bound
needed by the algebraic two-stage chart argument. -/
theorem equation_two_stage
    (slices : Fin g → R)
    [Module.Finite (Algebra.adjoin K (Set.range slices)) R]
    (base : I → R)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (B : Matrix (Fin b) (Fin l) (MvPolynomial (I ⊕ Fin n) K))
    (hcount : g < r+s) :
    ∃ P : MvPolynomial (Fin n ⊕ Fin l) K, P ≠ 0 ∧
      ∀ (φ : R →ₐ[K] K) (x : Fin n → K) (y : Fin l → K),
        r ≤ (evaluated A (fun i => φ (base i))).rank →
        s ≤ (evaluated B (Sum.elim (fun i => φ (base i)) x)).rank →
        evaluated A (fun i => φ (base i)) *ᵥ x = 0 →
        evaluated B (Sum.elim (fun i => φ (base i)) x) *ᵥ y = 0 →
        eval (Sum.elim x y) P = 0 := by
  let : Algebra.FiniteType K R :=
    AlgebraicDomainDimension.finiteType_of_finite_adjoin (K := K) slices
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  apply AlgebraicKernelAvoidance.equation_two_stage_components base _ A B hcount
  intro p hp
  let : p.IsPrime := hp.isPrime
  exact AlgebraicDomainDimension.trdeg_prime_quotient_le slices p

/-- An actual nonempty principal open excludes both dependent kernel
equations for every algebra point satisfying the actual rank conditions. -/
theorem principal_open_two_stage [Infinite K]
    (slices : Fin g → R)
    [Module.Finite (Algebra.adjoin K (Set.range slices)) R]
    (base : I → R)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (B : Matrix (Fin b) (Fin l) (MvPolynomial (I ⊕ Fin n) K))
    (hcount : g < r+s) :
    ∃ P : MvPolynomial (Fin n ⊕ Fin l) K,
      (∃ z : Fin n ⊕ Fin l → K, eval z P ≠ 0) ∧
      ∀ z, eval z P ≠ 0 → ∀ φ : R →ₐ[K] K,
        let t := fun i => φ (base i)
        let x := fun i => z (Sum.inl i)
        let y := fun j => z (Sum.inr j)
        r ≤ (evaluated A t).rank →
        s ≤ (evaluated B (Sum.elim t x)).rank →
        evaluated A t *ᵥ x ≠ 0 ∨ evaluated B (Sum.elim t x) *ᵥ y ≠ 0 := by
  let : Algebra.FiniteType K R :=
    AlgebraicDomainDimension.finiteType_of_finite_adjoin (K := K) slices
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  apply AlgebraicKernelAvoidance.principal_open_two_stage base _ A B hcount
  intro p hp
  let : p.IsPrime := hp.isPrime
  exact AlgebraicDomainDimension.trdeg_prime_quotient_le slices p

end Quartic.FiniteAlgebraicKernelAvoidance
