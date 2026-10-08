import Froberg.MatrixRankSpecialization

/-! # Matrix rank under extension of the ground field -/

noncomputable section
namespace Froberg
open Matrix Module

variable {K L m n : Type*} [Field K] [Field L]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- A rank-`r` matrix factors through a vector space of dimension `r`. -/
theorem exists_rank_factorization (M : Matrix m n K) :
    ∃ X : Matrix m (Fin M.rank) K, ∃ Y : Matrix (Fin M.rank) n K, M = X * Y := by
  let f := M.mulVecLin
  change ∃ X : Matrix m (Fin (finrank K f.range)) K,
    ∃ Y : Matrix (Fin (finrank K f.range)) n K, M = X * Y
  let b := Module.finBasis K f.range
  let x := f.range.subtype.comp b.equivFun.symm.toLinearMap
  let y := b.equivFun.toLinearMap.comp f.rangeRestrict
  refine ⟨LinearMap.toMatrix' x, LinearMap.toMatrix' y, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix' x, Matrix.toLin'_toMatrix' y]
  apply LinearMap.ext
  intro v
  change f v = (b.equivFun.symm (b.equivFun (f.rangeRestrict v))).val
  rw [b.equivFun.symm_apply_apply]
  rfl

/-- Scalar extension preserves matrix rank.  Both inequalities have
finite algebraic witnesses: a factorization and a nonsingular compression. -/
theorem matrix_rank_map_field (φ : K →+* L) (M : Matrix m n K) :
    (M.map φ).rank = M.rank := by
  apply Nat.le_antisymm
  · obtain ⟨X, Y, hM⟩ := exists_rank_factorization M
    have hfac : M.map φ = X.map φ * Y.map φ := by
      simpa only [Matrix.map_mul] using congrArg (fun A : Matrix m n K => A.map φ) hM
    rw [hfac]
    exact (Matrix.rank_mul_le_left _ _).trans
      (by simpa using Matrix.rank_le_card_width (X.map φ))
  · obtain ⟨X, Y, hYX⟩ := exists_rank_compression M
    apply rank_ge_of_compression_det_ne_zero (M.map φ) (X.map φ) (Y.map φ)
    have heq : Y.map φ * M.map φ * X.map φ = 1 := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, hYX]
      exact Matrix.map_one φ (map_zero φ) (map_one φ)
    rw [heq, Matrix.det_one]
    exact one_ne_zero

end Froberg
