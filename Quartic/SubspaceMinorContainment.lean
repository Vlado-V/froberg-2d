import Quartic.SubspaceMinorCoordinates

/-!
# Homogeneous containment equations for projective subspace coordinates

A varying presentation subspace can be required to lie inside a projectively
encoded plane using equations linear in the projective coordinates. This
lets quotient-subspace incidence be expressed in fixed ambient coordinates.
-/
noncomputable section
namespace Quartic.SubspaceMinorContainment
open Module Matrix SubspaceMinorCoordinates
variable {K : Type*} [Field K] {a d c : ℕ}

/-- Homogeneous Cramer equations saying that an ambient vector is contained. -/
def ContainsVector (p : RowChoice a d → K) (v : Fin a → K) : Prop :=
  ∀ J : RowChoice a d, p J • v = reconstruction p J *ᵥ (fun i => v (J i))

/-- Actual minor coordinates satisfy all containment equations, including
those with zero pivot coordinate. -/
theorem containsVector_coordinates (A : Matrix (Fin a) (Fin d) K)
    (v : Fin a → K) (hv : v ∈ LinearMap.range A.mulVecLin) :
    ContainsVector (coordinates A) v := by
  obtain ⟨x,rfl⟩ := hv
  intro J
  have he : (fun i => (A *ᵥ x) (J i)) = A.submatrix J id *ᵥ x := rfl
  change coordinates A J • (A *ᵥ x) = reconstruction (coordinates A) J *ᵥ (fun i => (A *ᵥ x) (J i))
  rw [he,reconstruction_coordinates]
  symm
  rw [← Matrix.mulVec_mulVec,Matrix.mulVec_mulVec x,Matrix.adjugate_mul,
    Matrix.smul_mulVec,Matrix.one_mulVec,Matrix.mulVec_smul]
  rfl

/-- At a nonzero pivot the containment equations give an actual coefficient
preimage in the reconstructed plane. -/
theorem mem_range_of_containsVector {p : RowChoice a d → K} {v : Fin a → K}
    (hv : ContainsVector p v) (J : RowChoice a d) (hJ : p J ≠ 0) :
    v ∈ LinearMap.range (reconstruction p J).mulVecLin := by
  refine ⟨(p J)⁻¹ • (fun i => v (J i)),?_⟩
  change reconstruction p J *ᵥ ((p J)⁻¹ • (fun i => v (J i))) = v
  rw [Matrix.mulVec_smul,← hv J,smul_smul,inv_mul_cancel₀ hJ,one_smul]

/-- Require each actual presentation column to satisfy the same homogeneous
containment equations. -/
def ContainsMatrix (p : RowChoice a d → K) (E : Matrix (Fin a) (Fin c) K) : Prop :=
  ∀ j : Fin c, ContainsVector p (fun i => E i j)

 theorem range_le_of_containsMatrix {p : RowChoice a d → K}
    (E : Matrix (Fin a) (Fin c) K) (hE : ContainsMatrix p E)
    (J : RowChoice a d) (hJ : p J ≠ 0) :
    LinearMap.range E.mulVecLin ≤ LinearMap.range (reconstruction p J).mulVecLin := by
  rintro _ ⟨x,rfl⟩
  rw [← (Pi.basisFun K (Fin c)).sum_equivFun x]
  simp only [map_sum,map_smul,Pi.basisFun_apply,Pi.basisFun_equivFun]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  have hc := mem_range_of_containsVector (hE j) J hJ
  have he : E.mulVecLin (Pi.single j 1) = (fun i => E i j) := by
    ext i
    simp
  rw [he]
  exact hc

/-- Projective minor coordinates also cover every plane containing a specified
presentation subspace. -/
theorem cover_containing [NeZero d] (S : Submodule K (Fin a → K))
    (hS : finrank K S = d) (E : Matrix (Fin a) (Fin c) K)
    (hE : LinearMap.range E.mulVecLin ≤ S) :
    ∃ p : RowChoice a d → K, p ≠ 0 ∧ Selected p ∧ ContainsMatrix p E ∧
      ∀ J, LinearMap.range (reconstruction p J).mulVecLin ≤ S := by
  classical
  obtain ⟨A,hA,J,hJ⟩ := exists_matrix S hS
  refine ⟨coordinates A,?_,(coordinates_valid A).selected,?_,?_⟩
  · intro hz
    have he := congrFun hz J
    rw [hJ] at he
    exact one_ne_zero he
  · intro j
    apply containsVector_coordinates
    rw [hA]
    apply hE
    refine ⟨Pi.single j 1,?_⟩
    ext i
    simp
  · intro H
    rw [← hA]
    exact reconstruction_range_le A H

end Quartic.SubspaceMinorContainment
