import Froberg.LinearPullback
import Froberg.SemilinearMatrices

/-! # Polynomial sections of linear representations -/

noncomputable section
namespace Froberg
open Matrix Module MvPolynomial

variable {K G P I : Type*} [Field K] [Infinite K] [Group G]
  [Fintype P] [DecidableEq P] [Fintype I] [DecidableEq I]

/-- Transport a representation to the coordinates of a specified basis. -/
def coordinateRepresentation {V : Type*} [AddCommGroup V] [Module K V]
    (b : Basis I K V) (ρ : Representation K G V) : Representation K G (I → K) :=
  b.equivFun.conjRingEquiv.toMonoidHom.comp ρ

@[simp] theorem coordinateRepresentation_apply {V : Type*}
    [AddCommGroup V] [Module K V] (b : Basis I K V)
    (ρ : Representation K G V) (g : G) (v : I → K) :
    coordinateRepresentation b ρ g v = b.equivFun (ρ g (b.equivFun.symm v)) := rfl

theorem coordinateRepresentation_toMatrix {V : Type*}
    [AddCommGroup V] [Module K V] (b : Basis I K V)
    (ρ : Representation K G V) (g : G) :
    LinearMap.toMatrix' (coordinateRepresentation b ρ g) = LinearMap.toMatrix b b (ρ g) := by
  ext i j
  rw [LinearMap.toMatrix'_apply, coordinateRepresentation_apply, LinearMap.toMatrix_apply]
  have hs : b.equivFun.symm (Pi.single j 1) = b j := by
    apply b.equivFun.injective
    ext k
    simp [Basis.equivFun_self, Pi.single_apply, eq_comm]
  rw [hs]
  rfl

/-- Pullback in the base and the given fiber representation define an
actual semilinear action on polynomial sections. -/
def polynomialSectionAction (ρP : Representation K G (P → K))
    (ρI : Representation K G (I → K)) :
    SemilinearMatrixAction K (MvPolynomial P K) G I where
  coeff := representationPullback ρP
  matrix g := (LinearMap.toMatrix' (ρI g)).map C
  matrix_one := by
    rw [map_one]
    simp only [Module.End.one_eq_id, LinearMap.toMatrix'_id]
    exact Matrix.map_one C (map_zero C) (map_one C)
  matrix_mul g h := by
    change (LinearMap.toMatrixAlgEquiv' (ρI (g * h))).map C = _
    rw [map_mul, map_mul, Matrix.map_mul]
    congr 1
    apply Matrix.ext
    intro i j
    exact (((representationPullback ρP) g).commutes _).symm

/-- Equality of evaluated covariance matrices implies equality of the
polynomial matrices themselves. -/
theorem polynomial_matrix_covariance_of_evaluation {J : Type*}
    [Fintype J] [DecidableEq J]
    (ρP : Representation K G (P → K)) (g : G)
    (M : Matrix I J (MvPolynomial P K)) (A : Matrix J J K) (B : Matrix I I K)
    (h : ∀ a : P → K, M.map (eval a) * A =
      B * M.map (eval (ρP g⁻¹ a))) :
    M * A.map C = B.map C * M.map (representationPullback ρP g) := by
  apply Matrix.ext
  intro i j
  apply MvPolynomial.funext
  intro a
  have hh := congrArg (fun N : Matrix I J K => N i j) (h a)
  simpa [Matrix.mul_apply, map_sum, map_mul, representationPullback_eval] using hh

end Froberg
