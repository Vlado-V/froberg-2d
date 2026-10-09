module

public import Froberg.WeightedParitySpace

@[expose] public section

/-! Two successive linear projections detect independence of a family
whose second block vanishes under the first projection. -/
noncomputable section
namespace Froberg
open Module
variable {K V W₀ W₁ I J : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W₀] [Module K W₀]
  [AddCommGroup W₁] [Module K W₁] [Fintype I] [Fintype J]

theorem two_step_linearIndependent (q : I → V) (v : J → V)
    (p₀ : V →ₗ[K] W₀) (p₁ : V →ₗ[K] W₁)
    (hq : LinearIndependent K (fun i => p₀ (q i)))
    (hv : LinearIndependent K (fun j => p₁ (v j)))
    (hz : ∀ j,p₀ (v j)=0) : LinearIndependent K (Sum.elim q v) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hqrel := congrArg p₀ hc
  simp only [map_sum,map_add,map_smul,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    hz,smul_zero,Finset.sum_const_zero,add_zero,map_zero] at hqrel
  have hcz : ∀ i,c (Sum.inl i)=0 := Fintype.linearIndependent_iff.mp hq _ hqrel
  have hvrel := congrArg p₁ hc
  simp only [map_sum,map_add,map_smul,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    hcz,zero_smul,Finset.sum_const_zero,zero_add,map_zero] at hvrel
  cases i with
  | inl i => exact hcz i
  | inr j => exact Fintype.linearIndependent_iff.mp hv _ hvrel j

end Froberg
