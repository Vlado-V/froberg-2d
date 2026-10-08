import Froberg.AffineSharedPolynomial
import Quartic.PolynomialSubspaceCovectorCharts

/-! Literal first-stage graph equations. Their higher-covector rank equals
the actual product-image dimension; adjoining the fixed bottom covector
cannot lower that rank. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module Matrix MvPolynomial Quartic Quartic.BilinearCovectorCharts
open Quartic.BilinearCoefficientKernel Quartic.KernelPolynomialCharts
variable {K I : Type*} [Field K] [Infinite K] [Fintype I]
variable {a b T T₀ N : ℕ}

def tupleProductConstraint
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (H : Fin N → Fin a → K) : (Fin T → K) →ₗ[K] (Fin (N*b) → K) :=
  LinearMap.pi fun l => covector (mu (Pi.single (finProdFinEquiv.symm l).2 1)
    (H (finProdFinEquiv.symm l).1))

@[simp] theorem tupleProductConstraint_apply
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (H : Fin N → Fin a → K) (ell : Fin T → K) (l : Fin (N*b)) :
    tupleProductConstraint mu H ell l=covector ell
      (mu (Pi.single (finProdFinEquiv.symm l).2 1) (H (finProdFinEquiv.symm l).1)) := by
  simp only [tupleProductConstraint,LinearMap.pi_apply,covector_apply,mul_comm]

def tupleProductConstraintLinear
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K)) :
    (Fin N → Fin a → K) →ₗ[K] ((Fin T → K) →ₗ[K] (Fin (N*b) → K)) where
  toFun := tupleProductConstraint mu
  map_add' H G := by
    apply LinearMap.ext
    intro ell
    funext l
    simp only [tupleProductConstraint_apply,LinearMap.add_apply,Pi.add_apply,map_add]
  map_smul' c H := by
    apply LinearMap.ext
    intro ell
    funext l
    simp only [tupleProductConstraint_apply,LinearMap.smul_apply,Pi.smul_apply,map_smul,RingHom.id_apply]

theorem tupleProductConstraint_rank
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (H : Fin N → Fin a → K) :
    finrank K (tupleProductConstraint mu H).range=
      finrank K (BilinearImage.image mu (Submodule.span K (Set.range H))) := by
  let HP : Fin N → Fin a → MvPolynomial Empty K := fun i j => C (H i j)
  let p : Empty → K := Empty.elim
  have hvec : PolynomialSubspaceCovectorCharts.vector HP p=H := by
    funext i j
    exact MvPolynomial.eval_C _
  have he : (evaluated (PolynomialSubspaceCovectorCharts.constraint mu HP) p).mulVecLin=
      tupleProductConstraint mu H := by
    apply LinearMap.ext
    intro ell
    funext l
    rw [Matrix.mulVecLin_apply,PolynomialSubspaceCovectorCharts.constraint_mulVec,
      tupleProductConstraint_apply]
    rw [hvec]
  have hr := PolynomialSubspaceCovectorCharts.constraint_rank mu HP p
  rw [Matrix.rank,he] at hr
  change finrank K (tupleProductConstraint mu H).range=
    finrank K (BilinearImage.image mu (Submodule.span K
      (Set.range (PolynomialSubspaceCovectorCharts.vector HP p)))) at hr
  rw [hvec] at hr
  exact hr

/-- Higher graph equations with the bottom contribution in one shared
homogenizing column. -/
def affineGraphConstraint
    (mu₀ : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T₀ → K))
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (H : Fin N → Fin a → K) (ell₀ : Fin T₀ → K) :
    ((Fin T → K) × K) →ₗ[K] (Fin (N*b) → K) :=
  affineHomogenization (tupleProductConstraint mu H) (tupleProductConstraint mu₀ H ell₀)

theorem affineGraphConstraint_rank
    (mu₀ : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T₀ → K))
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (H : Fin N → Fin a → K) (ell₀ : Fin T₀ → K) :
    finrank K (BilinearImage.image mu (Submodule.span K (Set.range H)))≤
      finrank K (affineGraphConstraint mu₀ mu H ell₀).range := by
  rw [←tupleProductConstraint_rank]
  exact affineHomogenization_rank _ _

theorem affineGraphConstraint_polynomial
    (mu₀ : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T₀ → K))
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (H : (I → K) → Fin N → Fin a → K) (ell₀ : (I → K) → Fin T₀ → K)
    (hH : IsPolynomialFamily H) (hell₀ : IsPolynomialFamily ell₀) :
    IsPolynomialFamily (fun p => affineGraphConstraint mu₀ mu (H p) (ell₀ p)) :=
  affineHomogenization_polynomial _ _
    (hH.linear_comp (tupleProductConstraintLinear mu))
    (hH.bilinear hell₀ (tupleProductConstraintLinear mu₀))

end Froberg
