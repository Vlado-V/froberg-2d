import Quartic.SubspaceCharts
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

/-!
# Kernel coordinates from actual pivot minors

For a chosen square minor, the selected kernel coordinates satisfy an
adjugate identity without any nonsingularity assumption. If the determinant
is nonzero, every kernel vector is reconstructed from its unselected
coordinates by the explicit rational formulas below. No generic-avoidance or
incidence-dimension assertion is made here.
-/
noncomputable section
namespace Quartic.KernelCharts
open Matrix Module SubspaceCharts
variable {K : Type*} [Field K] {a n r : ℕ}

/-- The actual square pivot minor. -/
def minor (A : Matrix (Fin a) (Fin n) K) (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) :
    Matrix (Fin r) (Fin r) K := A.submatrix u v

/-- Selected coordinates in their pivot order. -/
def selected (v : Fin r ↪ Fin n) (x : Fin n → K) : Fin r → K := fun i => x (v i)

/-- The unselected coordinates form the parameter vector. -/
def outside (v : Fin r ↪ Fin n) (x : Fin n → K) : Outside v → K := fun j => x j.val

/-- Contribution from the unselected columns in the selected row equations. -/
def offPivot (A : Matrix (Fin a) (Fin n) K) (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n)
    (y : Outside v → K) : Fin r → K := fun i => ∑ j, A (u i) j.val * y j

/-- Split a finite coordinate sum into its selected and unselected parts. -/
theorem sum_selected_add_outside (v : Fin r ↪ Fin n) (f : Fin n → K) :
    (∑ i, f (v i)) + (∑ j : Outside v, f j.val) = ∑ j, f j := by
  classical
  let : Fintype (Set.range v) := Subtype.fintype (fun j : Fin n => j ∈ Set.range v)
  have h := Fintype.sum_subtype_add_sum_subtype (fun j => j ∈ Set.range v) f
  have he : (∑ j : Set.range v, f j.val) = ∑ i, f (v i) := by
    exact ((Equiv.ofInjective v v.injective).sum_comp (fun j => f j.val)).symm
  exact (congrArg₂ (· + ·) he.symm rfl).trans h

/-- Selected row equations decompose into the pivot matrix and off-pivot contribution. -/
theorem selected_mulVec (A : Matrix (Fin a) (Fin n) K)
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (x : Fin n → K) :
    selected u (A *ᵥ x) = minor A u v *ᵥ selected v x + offPivot A u v (outside v x) := by
  funext i
  exact (sum_selected_add_outside v (fun j => A (u i) j * x j)).symm

/-- Every kernel vector satisfies the selected square system. -/
theorem kernel_pivot_equation (A : Matrix (Fin a) (Fin n) K)
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (x : Fin n → K) (hx : A *ᵥ x = 0) :
    minor A u v *ᵥ selected v x = -offPivot A u v (outside v x) := by
  have h := selected_mulVec A u v x
  rw [hx] at h
  have hz : selected u (0 : Fin a → K) = 0 := rfl
  rw [hz] at h
  exact eq_neg_iff_add_eq_zero.mpr h.symm

/-- The explicit adjugate identity holds even when the selected minor is singular. -/
theorem kernel_adjugate (A : Matrix (Fin a) (Fin n) K)
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (x : Fin n → K) (hx : A *ᵥ x = 0) :
    (minor A u v).det • selected v x =
      -(minor A u v).adjugate *ᵥ offPivot A u v (outside v x) := by
  have h := congrArg (fun z => (minor A u v).adjugate *ᵥ z)
    (kernel_pivot_equation A u v x hx)
  simpa only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_neg, Matrix.neg_mulVec] using h

/-- With a nonsingular minor, the pivot coordinates are minus its inverse
applied to the contribution of all remaining columns. -/
theorem kernel_selected_inverse (A : Matrix (Fin a) (Fin n) K)
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (hdet : (minor A u v).det ≠ 0)
    (x : Fin n → K) (hx : A *ᵥ x = 0) :
    selected v x = -(minor A u v)⁻¹ *ᵥ offPivot A u v (outside v x) := by
  have h := congrArg (fun z => (minor A u v)⁻¹ *ᵥ z)
    (kernel_pivot_equation A u v x hx)
  simpa only [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec,
    Matrix.mulVec_neg, Matrix.neg_mulVec] using h

/-- Coordinatewise adjugate-over-determinant reconstruction. -/
theorem kernel_selected_division (A : Matrix (Fin a) (Fin n) K)
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (hdet : (minor A u v).det ≠ 0)
    (x : Fin n → K) (hx : A *ᵥ x = 0) (i : Fin r) :
    x (v i) = -((minor A u v).adjugate *ᵥ offPivot A u v (outside v x)) i /
      (minor A u v).det := by
  apply (eq_div_iff hdet).mpr
  have h := congrFun (kernel_adjugate A u v x hx) i
  simpa only [Pi.smul_apply, smul_eq_mul, selected, Matrix.neg_mulVec, Pi.neg_apply,
    mul_comm] using h

/-- An explicit candidate vector determined by the unselected coordinates.
It satisfies every selected-row equation when the minor is nonsingular;
additional rows may impose further constraints on the parameter vector. -/
def reconstruct (A : Matrix (Fin a) (Fin n) K)
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (y : Outside v → K) : Fin n → K :=
  fun k => if h : k ∈ Set.range v then
    -((minor A u v).adjugate *ᵥ offPivot A u v y)
      ((Equiv.ofInjective v v.injective).symm ⟨k, h⟩) / (minor A u v).det
    else y ⟨k, h⟩

@[simp] theorem reconstruct_selected (A : Matrix (Fin a) (Fin n) K)
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (y : Outside v → K) (i : Fin r) :
    reconstruct A u v y (v i) =
      -((minor A u v).adjugate *ᵥ offPivot A u v y) i / (minor A u v).det := by
  classical
  simp [reconstruct]

@[simp] theorem reconstruct_outside (A : Matrix (Fin a) (Fin n) K)
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (y : Outside v → K) (j : Outside v) :
    reconstruct A u v y j.val = y j := by
  classical
  simp [reconstruct, j.property]

/-- Every vector in the kernel is exactly the rational reconstruction of its
n-r unselected coordinates. -/
theorem reconstruct_kernel (A : Matrix (Fin a) (Fin n) K)
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (hdet : (minor A u v).det ≠ 0)
    (x : Fin n → K) (hx : A *ᵥ x = 0) :
    reconstruct A u v (outside v x) = x := by
  classical
  funext k
  by_cases hk : k ∈ Set.range v
  · obtain ⟨i, rfl⟩ := hk
    rw [reconstruct_selected]
    exact (kernel_selected_division A u v hdet x hx i).symm
  · exact reconstruct_outside A u v (outside v x) ⟨k, hk⟩

/-- Restriction to the unselected coordinates is injective on the full kernel. -/
theorem outside_injective_on_kernel (A : Matrix (Fin a) (Fin n) K)
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (hdet : (minor A u v).det ≠ 0) :
    Function.Injective (fun x : LinearMap.ker A.mulVecLin => outside v x.val) := by
  intro x z h
  apply Subtype.ext
  rw [← reconstruct_kernel A u v hdet x.val x.property,
    ← reconstruct_kernel A u v hdet z.val z.property]
  exact congrArg (reconstruct A u v) h

/-- The chart uses exactly n-r scalar parameters. -/
theorem parameter_count (v : Fin r ↪ Fin n) : Fintype.card (Outside v) = n - r :=
  SubspaceCharts.card_outside v

/-- A rank lower bound selects that many linearly independent actual columns. -/
theorem exists_independent_columns (A : Matrix (Fin a) (Fin n) K) (hr : r ≤ A.rank) :
    ∃ v : Fin r ↪ Fin n, LinearIndependent K (fun j => A.col (v j)) := by
  classical
  obtain ⟨κ, f, hf, hspan, hli⟩ := exists_linearIndependent' K A.col
  let : Finite κ := Finite.of_injective f hf
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = A.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, ← hspan, finrank_span_eq_card hli]
  let b : Fin r ↪ κ :=
    (Fin.castLEEmb (by omega : r ≤ Fintype.card κ)).trans (Fintype.equivFin κ).symm.toEmbedding
  refine ⟨⟨fun j => f (b j), hf.comp b.injective⟩, ?_⟩
  exact hli.comp b b.injective

/-- Independent columns admit an equal-sized nonsingular minor using actual
ambient rows. This follows from coordinate charts on their span. -/
theorem exists_rows_for_independent_columns (A : Matrix (Fin a) (Fin n) K)
    (v : Fin r ↪ Fin n) (hv : LinearIndependent K (fun j => A.col (v j))) :
    ∃ u : Fin r ↪ Fin a, (minor A u v).det ≠ 0 := by
  classical
  let S : Submodule K (Fin a → K) := Submodule.span K (Set.range (fun j => A.col (v j)))
  have hS : finrank K S = r := by
    simpa only [S, Fintype.card_fin] using finrank_span_eq_card hv
  obtain ⟨u, e, he⟩ := exists_coordinate_equiv_of_finrank S hS
  let b : Fin r → S := fun j => ⟨A.col (v j), Submodule.subset_span ⟨j, rfl⟩⟩
  have hb : LinearIndependent K b := LinearIndependent.of_comp S.subtype hv
  have hi := hb.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  have hminor : LinearIndependent K (minor A u v).col := by
    convert hi using 1
    funext j i
    exact (he (b j) i).symm
  have hunit : IsUnit (minor A u v) :=
    Matrix.mulVec_injective_iff_isUnit.mp (Matrix.mulVec_injective_iff.mpr hminor)
  exact ⟨u, ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero⟩

/-- Every rank lower bound is witnessed by a nonzero actual r-by-r minor,
including the empty minor when r=0. -/
theorem exists_minor_of_rank_le (A : Matrix (Fin a) (Fin n) K) (hr : r ≤ A.rank) :
    ∃ u : Fin r ↪ Fin a, ∃ v : Fin r ↪ Fin n, (minor A u v).det ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_independent_columns A hr
  obtain ⟨u, hu⟩ := exists_rows_for_independent_columns A v hv
  exact ⟨u, v, hu⟩

end Quartic.KernelCharts
