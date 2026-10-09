module

public import Froberg.AttachedProjection

@[expose] public section

/-! Deficiency can occur only in a nonzero proper source subspace. -/
noncomputable section
namespace Froberg
open Module

/-- For a surjective linear map, zero and full source subspaces always have
maximal possible image dimension. -/
theorem deficient_projection_implies_proper
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (hf : Function.Surjective f) (U : Submodule K V)
    (hfail : finrank K (U.map f) < min (finrank K U) (finrank K W)) :
    0 < finrank K U ∧ finrank K U < finrank K V := by
  have hpos : 0 < finrank K U := lt_of_le_of_lt (Nat.zero_le _) (lt_of_lt_of_le hfail (min_le_left _ _))
  refine ⟨hpos,?_⟩
  have hle := Submodule.finrank_le U
  by_contra hn
  have he : finrank K U = finrank K V := by omega
  have htop : U = ⊤ := Submodule.eq_top_of_finrank_eq he
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hf
  rw [htop,Submodule.map_top,hrange,finrank_top] at hfail
  exact (not_lt_of_ge (min_le_right _ _)) hfail

end Froberg
