import Quartic.BilinearCovectorCharts
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Coefficient kernels of actual bilinear covectors

The matrix of conditions on one coefficient vector is the transpose of the
actual relation map on the source. Its rank is the source dimension minus
the actual relation-kernel dimension. Scaling the covector by a nonzero
scalar preserves both kernels and this rank.
-/
noncomputable section
namespace Quartic.BilinearCoefficientKernel
open Module Matrix BilinearCovectorCharts
variable {K : Type*} [Field K] {a b T : ℕ}
variable (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))

/-- The actual map R_ell, evaluated on every coefficient basis vector. -/
def relationMap (ell : Fin T → K) : (Fin a → K) →ₗ[K] (Fin b → K) :=
  LinearMap.pi fun f => (covector ell).comp (mu (Pi.single f 1))

@[simp] theorem relationMap_apply (ell : Fin T → K) (v : Fin a → K) (f : Fin b) :
    relationMap mu ell v f = covector ell (mu (Pi.single f 1) v) := rfl

/-- The coefficient equations, with one row per source basis vector. -/
def coefficientMatrix (ell : Fin T → K) : Matrix (Fin a) (Fin b) K :=
  fun v f => covector ell (mu (Pi.single f 1) (Pi.single v 1))

/-- Vary the coefficient vector and evaluate on every source basis vector. -/
def coefficientMap (ell : Fin T → K) : (Fin b → K) →ₗ[K] (Fin a → K) :=
  LinearMap.pi fun v => (covector ell).comp (mu.flip (Pi.single v 1))

@[simp] theorem coefficientMap_apply (ell : Fin T → K) (f : Fin b → K) (v : Fin a) :
    coefficientMap mu ell f v = covector ell (mu f (Pi.single v 1)) := rfl

/-- The coefficient matrix is literally the transpose of the actual R_ell matrix. -/
theorem coefficientMatrix_eq_transpose (ell : Fin T → K) :
    coefficientMatrix mu ell = (LinearMap.toMatrix' (relationMap mu ell)).transpose := by
  ext v f
  rfl

/-- It is also exactly the standard matrix of the coefficient map. -/
theorem coefficientMatrix_eq_toMatrix (ell : Fin T → K) :
    coefficientMatrix mu ell = LinearMap.toMatrix' (coefficientMap mu ell) := by
  ext v f
  rfl

@[simp] theorem coefficientMatrix_mulVec (ell : Fin T → K) (f : Fin b → K) :
    coefficientMatrix mu ell *ᵥ f = coefficientMap mu ell f := by
  rw [coefficientMatrix_eq_toMatrix, LinearMap.toMatrix'_mulVec]

/-- The matrix rank is the rank of the actual relation map. -/
theorem coefficientMatrix_rank (ell : Fin T → K) :
    (coefficientMatrix mu ell).rank = finrank K (LinearMap.range (relationMap mu ell)) := by
  rw [coefficientMatrix_eq_transpose, Matrix.rank_transpose, Matrix.rank]
  have h : (LinearMap.toMatrix' (relationMap mu ell)).mulVecLin = relationMap mu ell := by
    apply LinearMap.ext
    intro v
    exact LinearMap.toMatrix'_mulVec _ v
  rw [h]

/-- Rank-nullity relates the coefficient equations to the true relation kernel. -/
theorem coefficientMatrix_rank_add_kernel (ell : Fin T → K) :
    (coefficientMatrix mu ell).rank + finrank K (LinearMap.ker (relationMap mu ell)) = a := by
  rw [coefficientMatrix_rank, LinearMap.finrank_range_add_finrank_ker, Module.finrank_fin_fun]

/-- In particular the coefficient rank is a minus the actual kernel dimension. -/
theorem coefficientMatrix_rank_eq (ell : Fin T → K) :
    (coefficientMatrix mu ell).rank = a - finrank K (LinearMap.ker (relationMap mu ell)) := by
  have h := coefficientMatrix_rank_add_kernel mu ell
  omega

/-- Vanishing of the coefficient matrix is equivalent to vanishing on every source vector. -/
theorem coefficientMatrix_kernel_iff (ell : Fin T → K) (f : Fin b → K) :
    coefficientMatrix mu ell *ᵥ f = 0 ↔ ∀ v : Fin a → K, covector ell (mu f v) = 0 := by
  classical
  rw [coefficientMatrix_mulVec]
  constructor
  · intro hf v
    rw [← (Pi.basisFun K (Fin a)).sum_equivFun v]
    simp only [map_sum, map_smul, Pi.basisFun_apply, Pi.basisFun_equivFun]
    apply Finset.sum_eq_zero
    intro i _
    have hi : covector ell (mu f (Pi.single i 1)) = 0 := congrFun hf i
    rw [hi, smul_zero]
  · intro h
    funext i
    exact h (Pi.single i 1)

/-- The actual covector depends linearly on its coordinate array. -/
theorem covector_smul (s : K) (ell : Fin T → K) : covector (s • ell) = s • covector ell := by
  apply LinearMap.ext
  intro x
  simp only [covector_apply, Pi.smul_apply, smul_eq_mul, LinearMap.smul_apply,
    Finset.mul_sum, mul_assoc]

/-- The actual relation map has the same linear scaling. -/
theorem relationMap_smul (s : K) (ell : Fin T → K) :
    relationMap mu (s • ell) = s • relationMap mu ell := by
  apply LinearMap.ext
  intro v
  funext f
  simp only [relationMap_apply, covector_smul, LinearMap.smul_apply, Pi.smul_apply]

/-- Scaling a covector scales every coefficient equation. -/
theorem coefficientMatrix_smul (s : K) (ell : Fin T → K) :
    coefficientMatrix mu (s • ell) = s • coefficientMatrix mu ell := by
  ext v f
  simp only [coefficientMatrix, covector_smul, LinearMap.smul_apply, Matrix.smul_apply]

/-- Projectively equal nonzero covectors have the same true relation kernel. -/
theorem relationMap_kernel_smul (s : K) (hs : s ≠ 0) (ell : Fin T → K) :
    LinearMap.ker (relationMap mu (s • ell)) = LinearMap.ker (relationMap mu ell) := by
  ext v
  simp only [LinearMap.mem_ker, relationMap_smul, LinearMap.smul_apply,
    smul_eq_zero, hs, false_or]

/-- Scaling preserves the actual coefficient kernel as well. -/
theorem coefficientMatrix_kernel_smul (s : K) (hs : s ≠ 0) (ell : Fin T → K) :
    LinearMap.ker (coefficientMatrix mu (s • ell)).mulVecLin =
      LinearMap.ker (coefficientMatrix mu ell).mulVecLin := by
  ext f
  change coefficientMatrix mu (s • ell) *ᵥ f = 0 ↔ coefficientMatrix mu ell *ᵥ f = 0
  rw [coefficientMatrix_kernel_iff, coefficientMatrix_kernel_iff]
  simp only [covector_smul, LinearMap.smul_apply, smul_eq_zero, hs, false_or]

/-- The rank of the coefficient equations is projectively invariant. -/
theorem coefficientMatrix_rank_smul (s : K) (hs : s ≠ 0) (ell : Fin T → K) :
    (coefficientMatrix mu (s • ell)).rank = (coefficientMatrix mu ell).rank := by
  rw [coefficientMatrix_rank_eq, coefficientMatrix_rank_eq, relationMap_kernel_smul mu s hs ell]

/-- A prescribed relation-kernel dimension gives the exact coefficient rank. -/
theorem coefficientMatrix_rank_of_kernel_finrank (ell : Fin T → K) (d : ℕ)
    (hd : finrank K (LinearMap.ker (relationMap mu ell)) = d) :
    (coefficientMatrix mu ell).rank = a-d := by rw [coefficientMatrix_rank_eq, hd]

/-- The actual relation kernel is characterized without any choice of coefficient basis. -/
theorem relationMap_kernel_iff (ell : Fin T → K) (v : Fin a → K) :
    v ∈ LinearMap.ker (relationMap mu ell) ↔ ∀ f : Fin b → K, covector ell (mu f v) = 0 := by
  classical
  constructor
  · intro hv f
    rw [← (Pi.basisFun K (Fin b)).sum_equivFun f]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      Pi.basisFun_apply, Pi.basisFun_equivFun]
    apply Finset.sum_eq_zero
    intro i _
    have hi : covector ell (mu (Pi.single i 1) v) = 0 := congrFun hv i
    rw [hi, smul_zero]
  · intro hv
    funext f
    exact hv (Pi.single f 1)

/-- The full bilinear image of the true relation kernel is annihilated by the covector. -/
theorem kernel_image_annihilated (ell : Fin T → K) :
    BilinearImage.image mu (LinearMap.ker (relationMap mu ell)) ≤ LinearMap.ker (covector ell) := by
  apply iSup_le
  intro f
  rintro _ ⟨v,hv,rfl⟩
  exact (relationMap_kernel_iff mu ell v).mp hv f

/-- Source subspaces with annihilated full image are exactly subspaces of the relation kernel. -/
theorem image_annihilated_iff (ell : Fin T → K) (S : Submodule K (Fin a → K)) :
    BilinearImage.image mu S ≤ LinearMap.ker (covector ell) ↔ S ≤ LinearMap.ker (relationMap mu ell) := by
  constructor
  · intro h v hv
    apply (relationMap_kernel_iff mu ell v).mpr
    intro f
    exact h (BilinearImage.product_mem mu S f v hv)
  · intro h
    apply iSup_le
    intro f
    rintro _ ⟨v,hv,rfl⟩
    exact (relationMap_kernel_iff mu ell v).mp (h hv) f

open MvPolynomial KernelPolynomialCharts
variable {I : Type*}

/-- Actual polynomial coefficient equations for a polynomial covector numerator. -/
def polynomialMatrix (N : Fin T → MvPolynomial I K) :
    Matrix (Fin a) (Fin b) (MvPolynomial I K) :=
  fun v f => ∑ k, N k * C (mu (Pi.single f 1) (Pi.single v 1) k)

/-- Evaluation gives exactly the coefficient matrix of the evaluated covector. -/
theorem evaluated_polynomialMatrix (N : Fin T → MvPolynomial I K) (p : I → K) :
    evaluated (polynomialMatrix mu N) p = coefficientMatrix mu (fun k => eval p (N k)) := by
  ext v f
  simp [evaluated, polynomialMatrix, coefficientMatrix, covector_apply]

/-- The evaluated numerator is the common denominator times its rational covector. -/
theorem eval_covector_eq_smul_rationalMap (N : Fin T → MvPolynomial I K)
    (G : MvPolynomial I K) (p : I → K) (hG : eval p G ≠ 0) :
    (fun k => eval p (N k)) = eval p G • RationalImageAvoidance.rationalMap N G p := by
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, RationalImageAvoidance.rationalMap]
  field_simp

/-- The polynomial coefficient matrix and rational covector have identical rank off the denominator. -/
theorem evaluated_polynomialMatrix_rank (N : Fin T → MvPolynomial I K)
    (G : MvPolynomial I K) (p : I → K) (hG : eval p G ≠ 0) :
    (evaluated (polynomialMatrix mu N) p).rank =
      (coefficientMatrix mu (RationalImageAvoidance.rationalMap N G p)).rank := by
  rw [evaluated_polynomialMatrix, eval_covector_eq_smul_rationalMap N G p hG,
    coefficientMatrix_rank_smul mu _ hG]

/-- The polynomial equations have precisely the same coefficient kernel as the rational covector. -/
theorem evaluated_polynomialMatrix_kernel (N : Fin T → MvPolynomial I K)
    (G : MvPolynomial I K) (p : I → K) (hG : eval p G ≠ 0) :
    LinearMap.ker (evaluated (polynomialMatrix mu N) p).mulVecLin =
      LinearMap.ker (coefficientMatrix mu (RationalImageAvoidance.rationalMap N G p)).mulVecLin := by
  rw [evaluated_polynomialMatrix, eval_covector_eq_smul_rationalMap N G p hG,
    coefficientMatrix_kernel_smul mu _ hG]

end Quartic.BilinearCoefficientKernel
