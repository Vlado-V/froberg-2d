import Froberg.PolynomialFamilyRestoration

/-! Direct evaluation formulas for the polynomial restoration row avoid
unfolding its linear-map construction in downstream coefficient proofs. -/
noncomputable section
namespace Froberg.PolynomialRestoration
open MvPolynomial
variable {K : Type} [Field K]
variable {σ V Z : Type*} [AddCommGroup V] [Module K V]
variable [AddCommGroup Z] [Module K Z] {r : ℕ}

@[simp] theorem row_apply
    (j : V →ₗ[K] MvPolynomial σ K) (pi : MvPolynomial σ K →ₗ[K] Z)
    (q u : Fin r → V) :
    row j pi q u=pi (∑ i,j (q i)*j (u i)) := rfl

@[simp] theorem row_single
    (j : V →ₗ[K] MvPolynomial σ K) (pi : MvPolynomial σ K →ₗ[K] Z)
    (q : Fin r → V) (i : Fin r) (v : V) :
    row j pi q (Pi.single i v)=pi (j (q i)*j v) := by
  classical
  rw [row_apply]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro k hk hki
    simp [Pi.single_apply,hki]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

end Froberg.PolynomialRestoration
