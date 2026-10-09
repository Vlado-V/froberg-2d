module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic

@[expose] public section

/-!
# Polynomial matrices for exterior-power actions

The induced action on an exterior power is a matrix whose entries are
minors of the original matrix.  In particular it remains invertible over
the original coefficient ring and commutes with evaluation of coefficients.
-/

namespace Froberg

open Module Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Exterior-power matrix in the increasing-subset basis. -/
noncomputable def exteriorMatrix (r : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Set.powersetCard (Fin n) r) (Set.powersetCard (Fin n) r) R :=
  LinearMap.toMatrix ((Pi.basisFun R (Fin n)).exteriorPower r)
    ((Pi.basisFun R (Fin n)).exteriorPower r) (exteriorPower.map r A.toLin')

/-- This matrix computes the actual exterior-power action in coordinates. -/
theorem exteriorMatrix_mulVec_repr (r : ℕ) (A : Matrix (Fin n) (Fin n) R)
    (v : ⋀[R]^r (Fin n → R)) :
    exteriorMatrix r A *ᵥ ((Pi.basisFun R (Fin n)).exteriorPower r).repr v =
      ((Pi.basisFun R (Fin n)).exteriorPower r).repr (exteriorPower.map r A.toLin' v) :=
  LinearMap.toMatrix_mulVec_repr _ _ _ _

/-- Exterior-power matrices preserve the identity. -/
theorem exteriorMatrix_one (r : ℕ) :
    exteriorMatrix r (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  unfold exteriorMatrix
  rw [Matrix.toLin'_one, exteriorPower.map_id, LinearMap.toMatrix_id]

/-- Exterior-power matrices preserve multiplication. -/
theorem exteriorMatrix_mul (r : ℕ) (A B : Matrix (Fin n) (Fin n) R) :
    exteriorMatrix r (A * B) = exteriorMatrix r A * exteriorMatrix r B := by
  classical
  unfold exteriorMatrix
  rw [Matrix.toLin'_mul, exteriorPower.map_comp,
    LinearMap.toMatrix_comp ((Pi.basisFun R (Fin n)).exteriorPower r)
      ((Pi.basisFun R (Fin n)).exteriorPower r)
      ((Pi.basisFun R (Fin n)).exteriorPower r)]

/-- Thus an inverse over the coefficient ring gives an exterior-power
inverse over that same ring, with no localization. -/
theorem exteriorMatrix_left_inverse (r : ℕ) (A B : Matrix (Fin n) (Fin n) R)
    (hBA : B * A = 1) : exteriorMatrix r B * exteriorMatrix r A = 1 := by
  rw [← exteriorMatrix_mul, hBA, exteriorMatrix_one]

/-- Each exterior-power matrix entry is the corresponding minor. -/
theorem exteriorMatrix_apply (r : ℕ) (A : Matrix (Fin n) (Fin n) R)
    (s t : Set.powersetCard (Fin n) r) :
    exteriorMatrix r A s t =
      (A.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
        (Set.powersetCard.ofFinEmbEquiv.symm t)).det := by
  rw [exteriorMatrix, LinearMap.toMatrix_apply, exteriorPower.basis_repr_apply,
    exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family]
  rw [exteriorPower.ιMulti_family, exteriorPower.ιMultiDual_apply_ιMulti]
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp [Matrix.submatrix, Matrix.transpose, Basis.coord_apply,
    Matrix.toLin'_apply, Pi.basisFun_apply, Pi.basisFun_repr]

/-- Exterior-power matrices commute with any homomorphism of coefficient
rings, in particular specialization of polynomial parameters. -/
theorem exteriorMatrix_map {S : Type*} [CommRing S] (f : R →+* S)
    (r : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    exteriorMatrix r (A.map f) = (exteriorMatrix r A).map f := by
  ext s t
  rw [Matrix.map_apply, exteriorMatrix_apply, exteriorMatrix_apply]
  exact (f.map_det _).symm

end Froberg
