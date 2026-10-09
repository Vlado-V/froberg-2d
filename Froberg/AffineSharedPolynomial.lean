module

public import Froberg.AffineSharedCovectors

@[expose] public section

/-! Polynomial dependence of the literal affine common-scalar equations. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module Quartic Quartic.BilinearCovectorCharts
variable {K V W : Type*} [Field K] [Infinite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Affine homogenization is linear in its linear and constant terms. -/
def affineHomogenizationLinear : ((V →ₗ[K] W) × W) →ₗ[K] (V × K →ₗ[K] W) where
  toFun x := affineHomogenization x.1 x.2
  map_add' x y := by
    apply LinearMap.ext
    intro v
    simp only [affineHomogenization_apply,Prod.fst_add,Prod.snd_add,LinearMap.add_apply,smul_add]
    abel
  map_smul' c x := by
    apply LinearMap.ext
    intro v
    change (c • x.1) v.1 + v.2 • (c • x.2) = c • (x.1 v.1 + v.2 • x.2)
    simp only [LinearMap.smul_apply,smul_add]
    rw [smul_comm v.2 c]

variable {a b T q s : ℕ}

def fixedCovectorTermsLinear
    (B : Fin q → (Fin a → K) →ₗ[K] (Fin T → K)) :
    (Fin T → K) →ₗ[K] SharedCovectorPolynomial.Output K a q s :=
  (LinearMap.pi fun i => LinearMap.pi fun j => covector (B i (Pi.single j 1))).prod 0

@[simp] theorem fixedCovectorTermsLinear_apply
    (B : Fin q → (Fin a → K) →ₗ[K] (Fin T → K)) (ell : Fin T → K) :
    fixedCovectorTermsLinear (s := s) B ell=fixedCovectorTerms B ell := by
  apply Prod.ext
  · funext i j
    change covector (B i (Pi.single j 1)) ell=covector ell (B i (Pi.single j 1))
    simp only [covector_apply,mul_comm]
  · rfl

/-- One shared linear covector parameter controls every shifted scalar equation. -/
def affineSharedFamily
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (B : Fin q → (Fin a → K) →ₗ[K] (Fin T → K)) :
    (Fin T → K) →ₗ[K] ((SharedCovectorPolynomial.Input K b T q s × K) →ₗ[K]
      SharedCovectorPolynomial.Output K a q s) :=
  affineHomogenizationLinear.comp
    ((SharedCovectorPolynomial.family mu).prod (fixedCovectorTermsLinear B))

@[simp] theorem affineSharedFamily_apply
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (B : Fin q → (Fin a → K) →ₗ[K] (Fin T → K)) (ell : Fin T → K) :
    affineSharedFamily (s := s) mu B ell=affineSharedConstraint mu B ell := by
  change affineHomogenization (SharedCovectorPolynomial.family mu ell)
    (fixedCovectorTermsLinear B ell)=affineSharedConstraint mu B ell
  rw [fixedCovectorTermsLinear_apply]
  rfl

/-- Polynomial graph or affine-extension coordinates give polynomial matrices
for exactly the same common scalar family. -/
theorem affineSharedConstraint_polynomial {I : Type*} [Fintype I]
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (B : Fin q → (Fin a → K) →ₗ[K] (Fin T → K))
    (ell : (I → K) → (Fin T → K)) (hell : IsPolynomialFamily ell) :
    IsPolynomialFamily (fun t => affineSharedConstraint (s := s) mu B (ell t)) := by
  simpa only [affineSharedFamily_apply] using hell.linear_comp (affineSharedFamily (s := s) mu B)

end Froberg
