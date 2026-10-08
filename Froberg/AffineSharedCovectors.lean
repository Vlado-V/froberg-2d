import Froberg.AffinePolynomialAvoidance
import Quartic.SharedCovectorPolynomial

/-! The common scalar family retains all fixed positive-degree components.
One shared homogenizing coordinate handles these affine terms, while the
independent-equation rank includes every auxiliary covector slice. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module Quartic Quartic.BilinearCovectorCharts Quartic.BilinearCoefficientKernel
variable {K : Type*} [Field K] [Infinite K] {a b T q s : ℕ}

def fixedCovectorTerms (B : Fin q → (Fin a → K) →ₗ[K] (Fin T → K))
    (ell : Fin T → K) : SharedCovectorPolynomial.Output K a q s :=
  (fun i j => covector ell (B i (Pi.single j 1)),0)

def affineSharedConstraint
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (B : Fin q → (Fin a → K) →ₗ[K] (Fin T → K)) (ell : Fin T → K) :
    (SharedCovectorPolynomial.Input K b T q s × K) →ₗ[K]
      SharedCovectorPolynomial.Output K a q s :=
  affineHomogenization (SharedCovectorConstraints.constraint mu ell) (fixedCovectorTerms B ell)

/-- Fixed positive components cannot reduce the independent conditions
from the shared scalar family and the auxiliary slices. -/
theorem affineSharedConstraint_rank
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (B : Fin q → (Fin a → K) →ₗ[K] (Fin T → K)) (ell : Fin T → K) (hell : ell≠0) :
    q*(a-finrank K (relationMap mu ell).ker)+s≤
      finrank K (affineSharedConstraint (s := s) mu B ell).range := by
  rw [← SharedCovectorConstraints.rank mu ell hell]
  exact affineHomogenization_rank _ _

/-- At homogenizing coordinate one these are precisely annihilation of the
actual shifted generators, with the common scalar tuple unchanged. -/
theorem affineSharedConstraint_kernel_iff
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (B : Fin q → (Fin a → K) →ₗ[K] (Fin T → K)) (ell : Fin T → K)
    (x : SharedCovectorPolynomial.Input K b T q s) :
    affineSharedConstraint mu B ell (x,1)=0 ↔
      (∀ i v,covector ell (mu (x.1 i) v+B i v)=0) ∧
      (∀ j,covector ell (x.2 j)=0) := by
  classical
  constructor
  · intro hx
    constructor
    · intro i v
      have hb (j : Fin a) : covector ell (mu (x.1 i) (Pi.single j 1)+B i (Pi.single j 1))=0 := by
        have hh := congrFun (congrFun (congrArg Prod.fst hx) i) j
        simpa [affineSharedConstraint,affineHomogenization,fixedCovectorTerms,
          SharedCovectorConstraints.constraint,CoefficientConstraintRank.repeated,
          coefficientMap_apply,map_add] using hh
      rw [← (Pi.basisFun K (Fin a)).sum_equivFun v]
      simp only [map_sum,map_smul,Pi.basisFun_apply,Pi.basisFun_equivFun,
        ← Finset.sum_add_distrib,← smul_add]
      simp only [map_sum,map_smul,hb,smul_zero,Finset.sum_const_zero]
    · intro j
      have hh := congrFun (congrArg Prod.snd hx) j
      simpa [affineSharedConstraint,affineHomogenization,fixedCovectorTerms,
        SharedCovectorConstraints.constraint,CoefficientConstraintRank.repeated] using hh
  · rintro ⟨hgen,hcuts⟩
    apply Prod.ext
    · funext i j
      simpa [affineSharedConstraint,affineHomogenization,fixedCovectorTerms,
        SharedCovectorConstraints.constraint,CoefficientConstraintRank.repeated,
        coefficientMap_apply,map_add] using hgen i (Pi.single j 1)
    · funext j
      simpa [affineSharedConstraint,affineHomogenization,fixedCovectorTerms,
        SharedCovectorConstraints.constraint,CoefficientConstraintRank.repeated] using hcuts j

end Froberg
