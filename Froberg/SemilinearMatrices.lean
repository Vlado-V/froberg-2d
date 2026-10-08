import Froberg.ExteriorMatrix
import Froberg.PrimitiveVectors
import Mathlib.RepresentationTheory.Basic

/-!
# Semilinear matrix actions and their exterior powers

Coefficient automorphisms and covariance matrices with the twisted product
law define an honest linear representation over the ground ring.  Their
exterior-power matrices satisfy the same law.
-/

namespace Froberg

open Matrix

variable (k R G I : Type*) [CommRing k] [CommRing R] [Algebra k R]
  [Monoid G] [Fintype I] [DecidableEq I]

/-- Algebraic data of a group action on a free polynomial-coordinate
module: the matrix multiplication law twists the second matrix by the
coefficient automorphism of the first element. -/
structure SemilinearMatrixAction where
  coeff : G →* (R ≃ₐ[k] R)
  matrix : G → Matrix I I R
  matrix_one : matrix 1 = 1
  matrix_mul : ∀ g h, matrix (g * h) = matrix g * (matrix h).map (coeff g)

variable {k R G I}

/-- The associated action is linear over the ground ring. -/
noncomputable def SemilinearMatrixAction.toRepresentation
    (S : SemilinearMatrixAction k R G I) : Representation k G (I → R) where
  toFun g :=
    { toFun := fun v => S.matrix g *ᵥ (fun i => S.coeff g (v i))
      map_add' := by
        intro v w
        simp only [Pi.add_apply, map_add]
        exact Matrix.mulVec_add _ _ _
      map_smul' := by
        intro a v
        simpa only [Pi.smul_apply, Pi.smul_def, map_smul, RingHom.id_apply] using
          Matrix.mulVec_smul (S.matrix g) a (fun i => S.coeff g (v i)) }
  map_one' := by
    apply LinearMap.ext
    intro v
    funext i
    simp [S.matrix_one]
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro v
    funext i
    change (S.matrix (g * h) *ᵥ (fun j => S.coeff (g * h) (v j))) i =
      (S.matrix g *ᵥ (fun j => S.coeff g
        ((S.matrix h *ᵥ (fun t => S.coeff h (v t))) j))) i
    have hmap : (fun j => S.coeff g ((S.matrix h *ᵥ
        (fun t => S.coeff h (v t))) j)) =
        (S.matrix h).map (S.coeff g) *ᵥ (fun j => S.coeff g (S.coeff h (v j))) := by
      funext j
      exact (S.coeff g).toRingHom.map_mulVec _ _ j
    rw [hmap, Matrix.mulVec_mulVec, S.matrix_mul]
    simp only [map_mul, AlgEquiv.mul_apply]

/-- Coordinate formula for the constructed representation. -/
theorem SemilinearMatrixAction.toRepresentation_apply
    (S : SemilinearMatrixAction k R G I) (g : G) (v : I → R) :
    S.toRepresentation g v = S.matrix g *ᵥ (fun i => S.coeff g (v i)) := rfl

/-- Exterior powers preserve the complete twisted matrix product law. -/
noncomputable def SemilinearMatrixAction.exterior {n : ℕ}
    (S : SemilinearMatrixAction k R G (Fin n)) (r : ℕ) :
    SemilinearMatrixAction k R G (Set.powersetCard (Fin n) r) where
  coeff := S.coeff
  matrix := fun g => exteriorMatrix r (S.matrix g)
  matrix_one := by rw [S.matrix_one, exteriorMatrix_one]
  matrix_mul := by
    intro g h
    rw [S.matrix_mul, exteriorMatrix_mul]
    congr 1
    exact exteriorMatrix_map (S.coeff g).toRingHom r (S.matrix h)

section Group

variable {G' : Type*} [Group G']

/-- Covariance matrices are invertible over the original coefficient ring.
The explicit inverse uses the coefficient-twisted inverse group element. -/
theorem SemilinearMatrixAction.matrix_right_inverse
    (S : SemilinearMatrixAction k R G' I) (g : G') :
    S.matrix g * (S.matrix g⁻¹).map (S.coeff g) = 1 := by
  rw [← S.matrix_mul, mul_inv_cancel, S.matrix_one]

/-- The same explicit inverse is also a left inverse. -/
theorem SemilinearMatrixAction.matrix_left_inverse
    (S : SemilinearMatrixAction k R G' I) (g : G') :
    (S.matrix g⁻¹).map (S.coeff g) * S.matrix g = 1 :=
  mul_eq_one_comm.mp (S.matrix_right_inverse g)

/-- Primitive tuples stay primitive under the actual semilinear action. -/
theorem SemilinearMatrixAction.primitive_toRepresentation
    (S : SemilinearMatrixAction k R G' I)
    {v : I → R} (hv : IsPrimitiveVector v) (g : G') :
    IsPrimitiveVector (S.toRepresentation g v) := by
  rw [S.toRepresentation_apply]
  exact (hv.map (S.coeff g).toRingEquiv).mulVec
    (S.matrix g) ((S.matrix g⁻¹).map (S.coeff g)) (S.matrix_left_inverse g)

end Group

end Froberg
