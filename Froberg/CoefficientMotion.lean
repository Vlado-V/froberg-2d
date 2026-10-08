import Froberg.BilinearScalarFamily
import Froberg.CoefficientRank
import Quartic.BilinearMotionConstraints

/-! Actual scalar motions attached to an injected homology coefficient space.
The covector equations are literal polynomial matrices, with their exact
rank loss bounded by the source contraction kernel. -/
noncomputable section
namespace Froberg.CoefficientMotion
open Module Matrix MvPolynomial Quartic
open BilinearCovectorCharts BilinearCoefficientKernel KernelPolynomialCharts
variable {K H : Type*} [Field K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
variable {a b T f : ℕ}
variable (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
variable (E : H →ₗ[K] (Fin f → Fin a → K))

/-- The actual motion on the injected coefficient vectors. -/
def motion (z : Fin f → Fin b → K) : H →ₗ[K] (Fin T → K) :=
  (BilinearScalarFamily.multiplication mu z).comp E

@[simp] theorem motion_apply (z : Fin f → Fin b → K) (x : H) :
    motion mu E z x = ∑ i, mu (z i) (E x i) :=
  BilinearScalarFamily.multiplication_apply mu z (E x)

/-- A basis of H, represented by its genuine new-generator coefficients. -/
def columns : Fin (finrank K H) → Fin f → Fin a → K :=
  fun i => E (Module.finBasis K H i)

theorem columns_span_finrank (hE : Function.Injective E) :
    finrank K (Submodule.span K (Set.range (columns E))) = finrank K H := by
  have hi : LinearIndependent K (columns E) := (Module.finBasis K H).linearIndependent.map' E (LinearMap.ker_eq_bot.mpr hE)
  simpa using finrank_span_eq_card hi

/-- Matrix of all equations lambda(d_z x)=0 on basis vectors of H. -/
def constraint (ell : Fin T → K) : Matrix (Fin (finrank K H)) (Fin f × Fin b) K :=
  BilinearMotionConstraints.constraint mu ell (columns E)

/-- The polynomial matrix uses the same covector coordinates for every motion. -/
def polynomialConstraint :
    Matrix (Fin (finrank K H)) (Fin f × Fin b) (MvPolynomial (Fin T) K) :=
  BilinearMotionConstraints.polynomialConstraint mu X (fun j i v => C (columns E j i v))

@[simp] theorem evaluated_polynomialConstraint (ell : Fin T → K) :
    (polynomialConstraint mu E).map (eval ell) = constraint mu E ell := by
  have hh := BilinearMotionConstraints.eval_polynomialConstraint mu
    (fun k : Fin T => (X k : MvPolynomial (Fin T) K))
    (fun j i v => C (columns E j i v)) ell
  simpa only [eval_X,eval_C,polynomialConstraint,constraint] using hh

/-- Actual coefficient injectivity gives the a0-f*k equation bound of C.6. -/
theorem constraint_rank_bound (hE : Function.Injective E) (ell : Fin T → K) :
    finrank K H - f*finrank K (LinearMap.ker (relationMap mu ell)) ≤
      (constraint mu E ell).rank := by
  have hh := BilinearMotionConstraints.rank_bound mu ell (columns E)
  rwa [columns_span_finrank E hE] at hh

@[simp] theorem constraint_mulVec (ell : Fin T → K) (z : Fin f × Fin b → K)
    (i : Fin (finrank K H)) :
    (constraint mu E ell *ᵥ z) i =
      covector ell (motion mu E (fun j k => z (j,k)) (Module.finBasis K H i)) := by
  rw [motion_apply]
  exact BilinearMotionConstraints.mulVec_apply mu ell (columns E) z i

/-- Matrix vanishing is exactly annihilation of the actual motion map. -/
theorem constraint_kernel_iff (ell : Fin T → K) (z : Fin f × Fin b → K) :
    constraint mu E ell *ᵥ z = 0 ↔
      (covector ell).comp (motion mu E (fun j k => z (j,k))) = 0 := by
  constructor
  · intro hz
    apply (Module.finBasis K H).ext
    intro i
    exact (constraint_mulVec mu E ell z i).symm.trans (congrFun hz i)
  · intro hz
    funext i
    rw [constraint_mulVec]
    exact LinearMap.congr_fun hz (Module.finBasis K H i)

/-- Scaling the covector scales the whole literal constraint matrix. -/
theorem polynomialConstraint_scaling (c : K) (ell : Fin T → K) :
    (polynomialConstraint mu E).map (eval (c • ell)) =
      c • (polynomialConstraint mu E).map (eval ell) := by
  simp only [evaluated_polynomialConstraint]
  ext i j
  change covector (c • ell) (mu (Pi.single j.2 1) (columns E i j.1)) =
    c * covector ell (mu (Pi.single j.2 1) (columns E i j.1))
  rw [BilinearCoefficientKernel.covector_smul,LinearMap.smul_apply]
  rfl

/-- Finite indexing of the actual motion parameters. -/
abbrev MotionIndex (f b : ℕ) := Fin (Fintype.card (Fin f × Fin b))

def unflatten (z : MotionIndex f b → K) : Fin f → Fin b → K :=
  fun i j => z (Fintype.equivFin (Fin f × Fin b) (i,j))

def finiteConstraint (ell : Fin T → K) :
    Matrix (Fin (finrank K H)) (MotionIndex f b) K :=
  (constraint mu E ell).reindex (Equiv.refl _) (Fintype.equivFin (Fin f × Fin b))

def finitePolynomialConstraint :
    Matrix (Fin (finrank K H)) (MotionIndex f b) (MvPolynomial (Fin T) K) :=
  (polynomialConstraint mu E).reindex (Equiv.refl _) (Fintype.equivFin (Fin f × Fin b))

@[simp] theorem evaluated_finitePolynomialConstraint (ell : Fin T → K) :
    evaluated (finitePolynomialConstraint mu E) ell = finiteConstraint mu E ell := by
  ext i j
  exact congrFun (congrFun (evaluated_polynomialConstraint mu E ell) i)
    ((Fintype.equivFin (Fin f × Fin b)).symm j)

@[simp] theorem finiteConstraint_rank (ell : Fin T → K) :
    (finiteConstraint mu E ell).rank = (constraint mu E ell).rank :=
  Matrix.rank_reindex _ _ _

theorem finiteConstraint_mulVec (ell : Fin T → K) (z : MotionIndex f b → K) :
    finiteConstraint mu E ell *ᵥ z =
      constraint mu E ell *ᵥ (fun ij => unflatten z ij.1 ij.2) := by
  classical
  ext i
  apply Fintype.sum_equiv (Fintype.equivFin (Fin f × Fin b)).symm
  intro j
  simp [finiteConstraint,unflatten,Matrix.reindex_apply]

theorem finiteConstraint_kernel_iff (ell : Fin T → K) (z : MotionIndex f b → K) :
    finiteConstraint mu E ell *ᵥ z = 0 ↔
      (covector ell).comp (motion mu E (unflatten z)) = 0 := by
  rw [finiteConstraint_mulVec,constraint_kernel_iff]

end Froberg.CoefficientMotion
