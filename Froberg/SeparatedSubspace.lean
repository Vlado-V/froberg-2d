import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Coordinate-separated subspaces, independently of the chosen finite enumeration. -/
noncomputable section
namespace Froberg
open Module
variable {K I J : Type*} [Field K] [Fintype I] [DecidableEq I]
variable {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- The vectors allowed in one coordinate while all other coordinates are zero. -/
def coordinateSubmodule (R : Submodule K ((i : I) → V i)) (i : I) : Submodule K (V i) :=
  R.comap (LinearMap.single K _ i)

/-- A subspace closed under taking individual coordinates is the product of
its actual coordinate subspaces. -/
theorem eq_pi_coordinateSubmodule (R : Submodule K ((i : I) → V i))
    (hclosed : ∀ x ∈ R, ∀ i, Pi.single i (x i) ∈ R) :
    R = Submodule.pi Set.univ (coordinateSubmodule R) := by
  apply le_antisymm
  · intro x hx
    exact Submodule.mem_pi.mpr (fun i _ => hclosed x hx i)
  · intro x hx
    rw [← Finset.univ_sum_single x]
    exact Submodule.sum_mem _ (fun i _ => Submodule.mem_pi.mp hx i (Set.mem_univ i))

/-- Coordinate separation is preserved by every re-enumeration of the index set. -/
theorem eq_pi_of_reindex_eq_pi (q : J ≃ I) (R : Submodule K ((i : I) → V i))
    (D : (j : J) → Submodule K (V (q j)))
    (hR : R.map (LinearEquiv.piCongrLeft' K V q.symm).toLinearMap = Submodule.pi Set.univ D) :
    R = Submodule.pi Set.univ (coordinateSubmodule R) := by
  classical
  let e := LinearEquiv.piCongrLeft' K V q.symm
  apply eq_pi_coordinateSubmodule R
  intro x hx i
  have hx' : e x ∈ Submodule.pi Set.univ D := by
    rw [← hR]
    exact ⟨x,hx,rfl⟩
  have hy : e (Pi.single i (x i)) ∈ Submodule.pi Set.univ D := by
    apply Submodule.mem_pi.mpr
    intro j _
    by_cases hji : q j=i
    · subst i
      have hh := Submodule.mem_pi.mp hx' j (Set.mem_univ j)
      simpa only [e,LinearEquiv.piCongrLeft'_apply,q.symm_symm,Pi.single_eq_same] using hh
    · simpa only [e,LinearEquiv.piCongrLeft'_apply,q.symm_symm,Pi.single_eq_of_ne hji]
        using (D j).zero_mem
  rw [← hR] at hy
  obtain ⟨z,hz,heq⟩ := hy
  exact e.injective heq ▸ hz

/-- The product of coordinate submodules is linearly equivalent to their
coordinatewise product. -/
def coordinatePiEquiv (C : (i : I) → Submodule K (V i)) :
    (Submodule.pi Set.univ C) ≃ₗ[K] ((i : I) → C i) where
  toFun x i := ⟨x.val i,Submodule.mem_pi.mp x.property i (Set.mem_univ i)⟩
  invFun x := ⟨fun i => (x i).val,Submodule.mem_pi.mpr (fun i _ => (x i).property)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := funext (fun _ => Subtype.ext rfl)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_coordinate_pi [∀ i, FiniteDimensional K (V i)]
    (C : (i : I) → Submodule K (V i)) :
    finrank K (Submodule.pi Set.univ C) = ∑ i, finrank K (C i) := by
  rw [(coordinatePiEquiv C).finrank_eq,Module.finrank_pi_fintype]

end Froberg
