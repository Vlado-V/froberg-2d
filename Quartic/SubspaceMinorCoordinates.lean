import Quartic.SubspaceCharts
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Finite homogeneous projective coordinates for subspaces

Coordinates are indexed by all ordered row choices, including repeated rows.
This redundant indexing avoids sign conventions. Cramer's rule reconstructs
spanning columns linearly in the coordinates. Homogeneous determinant identities
characterize the nonzero arrays needed for projective incidence arguments.
-/
noncomputable section
namespace Quartic.SubspaceMinorCoordinates
open Module Matrix
variable {K : Type*} [Field K] {a d : ℕ}

abbrev RowChoice (a d : ℕ) := Fin d → Fin a

def coordinates (A : Matrix (Fin a) (Fin d) K) (J : RowChoice a d) : K :=
  (A.submatrix J id).det

def reconstruction (p : RowChoice a d → K) (J : RowChoice a d) : Matrix (Fin a) (Fin d) K :=
  fun k i => p (Function.update J i k)

/-- Cramer's row-replacement determinants give the actual adjugate columns. -/
theorem reconstruction_coordinates (A : Matrix (Fin a) (Fin d) K) (J : RowChoice a d) :
    reconstruction (coordinates A) J = A * (A.submatrix J id).adjugate := by
  classical
  ext k i
  have hupdate : A.submatrix (Function.update J i k) id = (A.submatrix J id).updateRow i (A k) := by
    ext h l
    change A (Function.update J i k h) l = (Function.update (fun h l => A (J h) l) i (A k)) h l
    by_cases hh : h = i <;> simp [hh]
  change (A.submatrix (Function.update J i k) id).det = _
  rw [hupdate,← Matrix.cramer_transpose_apply,Matrix.cramer_eq_adjugate_mulVec,← Matrix.adjugate_transpose]
  simp [Matrix.mulVec,Matrix.mul_apply,dotProduct,mul_comm]

/-- Selected coordinate identities are linear and already suffice to
reconstruct a d-plane at every nonzero pivot. -/
def Selected (p : RowChoice a d → K) : Prop :=
  ∀ J : RowChoice a d, ∀ i j : Fin d,
    reconstruction p J (J i) j = if i = j then p J else 0

/-- Additional determinant identities satisfied by actual minor arrays. -/
structure Valid (p : RowChoice a d → K) : Prop where
  selected : ∀ J : RowChoice a d, ∀ i j : Fin d,
    reconstruction p J (J i) j = if i = j then p J else 0
  minors : ∀ J H : RowChoice a d,
    ((reconstruction p J).submatrix H id).det = p H * (p J)^(d-1)

/-- Every actual list of row minors satisfies the finite homogeneous system. -/
theorem coordinates_valid [NeZero d] (A : Matrix (Fin a) (Fin d) K) : Valid (coordinates A) := by
  constructor
  · intro J i j
    have h := congrFun (congrFun (Matrix.mul_adjugate (A.submatrix J id)) i) j
    rw [reconstruction_coordinates]
    change (A.submatrix J id * (A.submatrix J id).adjugate) i j = _
    rw [h]
    simp [coordinates,Matrix.one_apply]
  · intro J H
    rw [reconstruction_coordinates]
    have he : (A * (A.submatrix J id).adjugate).submatrix H id =
        A.submatrix H id * (A.submatrix J id).adjugate := by
      ext i j
      rfl
    rw [he,Matrix.det_mul,Matrix.det_adjugate]
    simp only [Fintype.card_fin]
    rfl

/-- A nonzero pivot coordinate gives an injective reconstructed coefficient map. -/
theorem reconstruction_injective_of_selected {p : RowChoice a d → K} (hp : Selected p)
    (J : RowChoice a d) (hJ : p J ≠ 0) : Function.Injective (reconstruction p J).mulVecLin := by
  unfold Selected at hp
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro x hx
    change x = 0
    funext i
    have he := congrFun hx (J i)
    change ∑ j, reconstruction p J (J i) j * x j = 0 at he
    simp [hp] at he
    exact he.resolve_left hJ
  · exact bot_le

theorem reconstruction_injective {p : RowChoice a d → K} (hp : Valid p)
    (J : RowChoice a d) (hJ : p J ≠ 0) : Function.Injective (reconstruction p J).mulVecLin :=
  reconstruction_injective_of_selected hp.selected J hJ

/-- Selected identities alone give the prescribed dimension. -/
theorem reconstruction_finrank_of_selected {p : RowChoice a d → K} (hp : Selected p)
    (J : RowChoice a d) (hJ : p J ≠ 0) :
    finrank K (LinearMap.range (reconstruction p J).mulVecLin) = d := by
  rw [LinearMap.finrank_range_of_inj (reconstruction_injective_of_selected hp J hJ),Module.finrank_fin_fun]

/-- The reconstructed subspace has the prescribed dimension. -/
theorem reconstruction_finrank {p : RowChoice a d → K} (hp : Valid p)
    (J : RowChoice a d) (hJ : p J ≠ 0) :
    finrank K (LinearMap.range (reconstruction p J).mulVecLin) = d := by
  rw [LinearMap.finrank_range_of_inj (reconstruction_injective hp J hJ),Module.finrank_fin_fun]

/-- Every reconstructed column belongs to the original subspace, including
charts whose pivot coordinate vanishes. -/
theorem reconstruction_range_le (A : Matrix (Fin a) (Fin d) K) (J : RowChoice a d) :
    LinearMap.range (reconstruction (coordinates A) J).mulVecLin ≤ LinearMap.range A.mulVecLin := by
  rw [reconstruction_coordinates]
  rintro _ ⟨x,rfl⟩
  exact ⟨(A.submatrix J id).adjugate *ᵥ x,Matrix.mulVec_mulVec x A (A.submatrix J id).adjugate⟩

/-- Every actual d-plane has a matrix of spanning columns with a unit row minor. -/
theorem exists_matrix (S : Submodule K (Fin a → K)) (hS : finrank K S = d) :
    ∃ A : Matrix (Fin a) (Fin d) K, LinearMap.range A.mulVecLin = S ∧
      ∃ J : RowChoice a d, coordinates A J = 1 := by
  classical
  obtain ⟨j,e,he⟩ := SubspaceCharts.exists_coordinate_equiv_of_finrank S hS
  let f := S.subtype.comp e.symm.toLinearMap
  let A := LinearMap.toMatrix' f
  have hA : A.mulVecLin = f := by
    apply LinearMap.ext
    intro x
    exact LinearMap.toMatrix'_mulVec _ x
  have hrange : LinearMap.range A.mulVecLin = S := by
    rw [hA]
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact (e.symm y).property
    · intro hx
      refine ⟨e ⟨x,hx⟩,?_⟩
      simp [f]
  have hpivot : A.submatrix j id = 1 := by
    ext i k
    change (e.symm (Pi.single k 1)).val (j i) = _
    rw [← he,e.apply_symm_apply]
    simp [Matrix.one_apply,Pi.single_apply]
  refine ⟨A,hrange,j,?_⟩
  exact (congrArg Matrix.det hpivot).trans Matrix.det_one

/-- Actual minor arrays cover all d-planes and every one of their reconstructed
column spaces stays in the original plane, even at zero pivots. -/
theorem cover_subspace [NeZero d] (S : Submodule K (Fin a → K)) (hS : finrank K S = d) :
    ∃ p : RowChoice a d → K, p ≠ 0 ∧ Selected p ∧
      (∀ J, LinearMap.range (reconstruction p J).mulVecLin ≤ S) := by
  obtain ⟨A,hA,J,hJ⟩ := exists_matrix S hS
  refine ⟨coordinates A,?_,(coordinates_valid A).selected,?_⟩
  · intro hz
    have he := congrFun hz J
    rw [hJ] at he
    exact one_ne_zero he
  · intro H
    rw [← hA]
    exact reconstruction_range_le A H

end Quartic.SubspaceMinorCoordinates
