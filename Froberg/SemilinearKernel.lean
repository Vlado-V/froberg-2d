module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic

@[expose] public section

/-!
# Kernels and images of covariant polynomial matrices

A commuting semilinear matrix square acts on the actual kernel and image
of the matrix.  This is the linear algebra used for the universal complex.
-/

namespace Froberg

open Matrix

variable {R m n : Type*} [CommRing R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- Applying a coefficient automorphism to the entries and to a vector
commutes with matrix multiplication. -/
theorem map_matrix_mulVec (e : R ≃+* R) (M : Matrix m n R) (v : n → R) :
    M.map e *ᵥ (fun i => e (v i)) = fun i => e ((M *ᵥ v) i) := by
  funext i
  exact (e.toRingHom.map_mulVec M v i).symm

omit [DecidableEq m] [DecidableEq n] in
/-- A semilinear covariance square gives the corresponding identity on
vectors without choosing bases of kernels or images. -/
theorem semilinear_covariance_apply
    (e : R ≃+* R) (M : Matrix m n R)
    (A : Matrix n n R) (B : Matrix m m R)
    (hcov : M * A = B * M.map e) (v : n → R) :
    M *ᵥ (A *ᵥ (fun i => e (v i))) =
      B *ᵥ (fun i => e ((M *ᵥ v) i)) := by
  rw [Matrix.mulVec_mulVec, hcov, ← Matrix.mulVec_mulVec, map_matrix_mulVec]

/-- The actual kernel is stable under any covariant semilinear action. -/
theorem semilinear_matrix_kernel_covariant
    (e : R ≃+* R) (M : Matrix m n R)
    (A : Matrix n n R) (B : Matrix m m R)
    (hcov : M * A = B * M.map e)
    {v : n → R} (hv : v ∈ LinearMap.ker M.mulVecLin) :
    A *ᵥ (fun i => e (v i)) ∈ LinearMap.ker M.mulVecLin := by
  change M *ᵥ (A *ᵥ (fun i => e (v i))) = 0
  change M *ᵥ v = 0 at hv
  rw [semilinear_covariance_apply e M A B hcov, hv]
  simp only [Pi.zero_apply, map_zero]
  exact Matrix.mulVec_zero B

/-- The actual image is stable under the same covariance square. -/
theorem semilinear_matrix_image_covariant
    (e : R ≃+* R) (M : Matrix m n R)
    (A : Matrix n n R) (B : Matrix m m R)
    (hcov : M * A = B * M.map e)
    {w : m → R} (hw : w ∈ LinearMap.range M.mulVecLin) :
    B *ᵥ (fun i => e (w i)) ∈ LinearMap.range M.mulVecLin := by
  obtain ⟨v, rfl⟩ := hw
  exact ⟨A *ᵥ (fun i => e (v i)), semilinear_covariance_apply e M A B hcov v⟩

end Froberg
