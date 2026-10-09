module

public import Quartic.SharedCovectorConstraints
public import Quartic.PolynomialBilinearCoordinates
public import Quartic.PolynomialKernelAvoidance

@[expose] public section

/-!
# Polynomial shared-coefficient and auxiliary-slice constraints

The actual simultaneous covector equations are a linear family in the
covector. Their coordinate matrix therefore has literal polynomial entries
when the covector is represented by polynomial numerators. Its rank includes
the exact auxiliary-slice contribution for every nonzero covector.
-/
noncomputable section
namespace Quartic.SharedCovectorPolynomial
open Module Matrix MvPolynomial BilinearCoefficientKernel BilinearCovectorCharts
open PolynomialBilinearCoordinates KernelPolynomialCharts
variable {K I : Type*} [Field K] {a b T q e : ℕ}

abbrev Input (K : Type*) [Field K] (b T q e : ℕ) :=
  (Fin q → Fin b → K) × (Fin e → Fin T → K)
abbrev Output (K : Type*) [Field K] (a q e : ℕ) :=
  (Fin q → Fin a → K) × (Fin e → K)

/-- The actual shared and sliced equations depend linearly on the covector. -/
def family (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K)) :
    (Fin T → K) →ₗ[K] Input K b T q e →ₗ[K] Output K a q e where
  toFun := SharedCovectorConstraints.constraint mu
  map_add' ell ell' := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · funext i v
      change covector (ell+ell') (mu (x.1 i) (Pi.single v 1))=
        covector ell (mu (x.1 i) (Pi.single v 1))+covector ell' (mu (x.1 i) (Pi.single v 1))
      simp only [covector_apply,Pi.add_apply,add_mul,Finset.sum_add_distrib]
    · funext i
      change covector (ell+ell') (x.2 i)=covector ell (x.2 i)+covector ell' (x.2 i)
      simp only [covector_apply,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' c ell := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · funext i v
      change covector (c • ell) (mu (x.1 i) (Pi.single v 1))=
        c • covector ell (mu (x.1 i) (Pi.single v 1))
      rw [covector_smul,LinearMap.smul_apply]
    · funext i
      change covector (c • ell) (x.2 i)=c • covector ell (x.2 i)
      rw [covector_smul,LinearMap.smul_apply]

def polynomialMatrix (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (N : Fin T → MvPolynomial I K) :
    Matrix (Fin (finrank K (Output K a q e))) (Fin (finrank K (Input K b T q e)))
      (MvPolynomial I K) :=
  fun i j => ∑ k : Fin T,N k*C ((coordinate (family (q := q) (e := e) mu)
    (Pi.single k 1)) (Pi.single j 1) i)

/-- Literal polynomial evaluation gives the matrix of the actual simultaneous equations. -/
theorem evaluated_polynomialMatrix
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (N : Fin T → MvPolynomial I K) (p : I → K) :
    evaluated (polynomialMatrix (q := q) (e := e) mu N) p=
      LinearMap.toMatrix' (coordinate (family (q := q) (e := e) mu) (fun k => eval p (N k))) := by
  classical
  ext i j
  change eval p (∑ k : Fin T,N k*C ((coordinate (family mu) (Pi.single k 1)) (Pi.single j 1) i))=_
  rw [map_sum]
  conv_rhs => rw [←(Pi.basisFun K (Fin T)).sum_equivFun (fun k => eval p (N k))]
  simp only [map_mul,eval_C,map_sum,map_smul,LinearMap.toMatrix'_apply,LinearMap.sum_apply,
    LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply,Pi.basisFun_apply,Pi.basisFun_equivFun,
    LinearEquiv.refl_apply,smul_eq_mul]

/-- The exact codimension includes one independent condition for every auxiliary slice. -/
theorem polynomialMatrix_rank
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (N : Fin T → MvPolynomial I K) (p : I → K)
    (hN : (fun k => eval p (N k)) ≠ 0) :
    (evaluated (polynomialMatrix (q := q) (e := e) mu N) p).rank=
      q*(a-finrank K (LinearMap.ker (relationMap mu (fun k => eval p (N k)))))+e := by
  rw [evaluated_polynomialMatrix,Matrix.rank]
  have he : (LinearMap.toMatrix' (coordinate (family (q := q) (e := e) mu)
      (fun k => eval p (N k)))).mulVecLin=
      coordinate (family (q := q) (e := e) mu) (fun k => eval p (N k)) := by
    apply LinearMap.ext
    intro x
    exact LinearMap.toMatrix'_mulVec _ x
  rw [he,finrank_range_coordinate]
  exact SharedCovectorConstraints.rank mu _ hN

/-- Coordinate multiplication is exactly the original shared Q and auxiliary constraints. -/
theorem polynomialMatrix_mulVec
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (N : Fin T → MvPolynomial I K) (p : I → K) (x : Input K b T q e) :
    evaluated (polynomialMatrix (q := q) (e := e) mu N) p *ᵥ
      (coordinates K (Input K b T q e) x)=
        coordinates K (Output K a q e) (SharedCovectorConstraints.constraint mu
          (fun k => eval p (N k)) x) := by
  rw [evaluated_polynomialMatrix,LinearMap.toMatrix'_mulVec]
  simp only [coordinate_apply,LinearEquiv.symm_apply_apply]
  rfl

/-- In particular, the polynomial kernel condition is equivalent to the actual
covector annihilating the shared products and every auxiliary slice. -/
theorem polynomialMatrix_kernel_iff
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (N : Fin T → MvPolynomial I K) (p : I → K) (x : Input K b T q e) :
    evaluated (polynomialMatrix (q := q) (e := e) mu N) p *ᵥ
      (coordinates K (Input K b T q e) x)=0 ↔
      (∀ i v,covector (fun k => eval p (N k)) (mu (x.1 i) v)=0) ∧
      (∀ j,covector (fun k => eval p (N k)) (x.2 j)=0) := by
  rw [polynomialMatrix_mulVec,LinearEquiv.map_eq_zero_iff,SharedCovectorConstraints.kernel_iff]

end Quartic.SharedCovectorPolynomial
