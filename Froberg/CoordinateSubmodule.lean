module

public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Tactic

@[expose] public section

/-! A relation space preserved by all coordinate projections is exactly
the product of its coordinate relation spaces. The resulting quotient
splitting retains every coordinate, including coordinates with no source. -/
noncomputable section
namespace Froberg
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
variable {V : I → Type*} [∀ i,AddCommGroup (V i)] [∀ i,Module K (V i)]

theorem coordinate_submodule_eq (R : Submodule K ((i : I) → V i))
    (hR : ∀ x∈R,∀ i,Pi.single i (x i)∈R) :
    R=Submodule.pi Set.univ (fun i => R.map (LinearMap.proj i)) := by
  ext x
  constructor
  · intro hx
    exact Submodule.mem_pi.mpr (fun i _ => ⟨x,hx,rfl⟩)
  · intro hx
    have hi (i : I) : Pi.single i (x i)∈R := by
      obtain ⟨y,hy,he⟩ := Submodule.mem_pi.mp hx i (Set.mem_univ i)
      have hh := hR y hy i
      change y i=x i at he
      rw [he] at hh
      exact hh
    have hs : (∑ i,Pi.single i (x i))=x := by
      funext j
      simp
    rw [←hs]
    exact Submodule.sum_mem R (fun i _ => hi i)

def coordinateRelation (R : Submodule K ((i : I) → V i)) (i : I) : Submodule K (V i) :=
  R.map (LinearMap.proj i)

def coordinateQuotientEquiv (R : Submodule K ((i : I) → V i))
    (hR : ∀ x∈R,∀ i,Pi.single i (x i)∈R) :
    (((i : I) → V i) ⧸ R) ≃ₗ[K] ((i : I) → (V i ⧸ coordinateRelation R i)) :=
  (Submodule.quotEquivOfEq _ _ (coordinate_submodule_eq R hR)).trans
    (Submodule.quotientPi (fun i => coordinateRelation R i))

end Froberg
