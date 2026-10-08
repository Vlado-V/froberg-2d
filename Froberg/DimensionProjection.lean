import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! A dimension bound supplies an actual linear projection. -/
noncomputable section
namespace Froberg
open Module
variable {K V W : Type*} [Field K]
  [AddCommMonoid V] [Module K V] [Module.Finite K V]
  [AddCommMonoid W] [Module K W] [Module.Finite K W]

theorem exists_surjective_linearMap_of_finrank_le (h : finrank K W ≤ finrank K V) :
    ∃ P : V →ₗ[K] W, Function.Surjective P := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  obtain ⟨i, hi⟩ := finrank_le_iff_exists_linearMap.mp h
  obtain ⟨P, hP⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  refine ⟨P, fun w => ⟨i w, ?_⟩⟩
  exact congrArg (fun f : W →ₗ[K] W => f w) hP

end Froberg
