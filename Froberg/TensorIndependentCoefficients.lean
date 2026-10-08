import Froberg.TensorQuotientCoordinates
import Froberg.MixedQuotientExactness
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Independent left tensor factors detect each right-factor relation. -/
noncomputable section
namespace Froberg
open Module TensorProduct Quartic.SplitTensor
attribute [local instance] tensorQuotientGroup
variable {K X Y I : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y] [Fintype I]

def rightTensorCoefficient (e : X →ₗ[K] K) : X ⊗[K] Y →ₗ[K] Y :=
  (TensorProduct.lid K Y).toLinearMap.comp (TensorProduct.map e LinearMap.id)

@[simp] theorem rightTensorCoefficient_tmul (e : X →ₗ[K] K) (x : X) (y : Y) :
    rightTensorCoefficient e (x ⊗ₜ[K] y)=e x • y := rfl

theorem rightTensorCoefficient_mem (S : Submodule K Y) (e : X →ₗ[K] K)
    (z : X ⊗[K] Y) (hz : z∈rightRelations S) : rightTensorCoefficient e z∈S := by
  obtain ⟨w,rfl⟩ := hz
  induction w using TensorProduct.inductionOn with
  | tmul x y =>
    change e x • y.val∈S
    exact S.smul_mem _ y.property
  | add v w hv hw =>
    simpa only [map_add] using S.add_mem hv hw

theorem independent_tensor_coefficients_mem (U : I → X) (hU : LinearIndependent K U)
    (S : Submodule K Y) (v : I → Y) (hv : (∑ j,U j ⊗ₜ[K] v j)∈rightRelations S) :
    ∀ i,v i∈S := by
  classical
  obtain ⟨L,hL⟩ := (Fintype.linearCombination K U).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hU.fintypeLinearCombination_injective)
  have hLU (j : I) : L (U j)=Pi.single j 1 := by
    have he := LinearMap.congr_fun hL (Pi.single j 1)
    simpa [Fintype.linearCombination_apply] using he
  intro i
  have hm := rightTensorCoefficient_mem S ((LinearMap.proj i).comp L) _ hv
  simp only [map_sum,rightTensorCoefficient_tmul,LinearMap.comp_apply,
    LinearMap.proj_apply,hLU] at hm
  simpa [Pi.single_apply] using hm

theorem separated_tensor_coefficients_mem (U : I → X) (hU : LinearIndependent K U)
    (S : Submodule K Y) (E : Submodule K (X ⊗[K] Y))
    (hE : Disjoint E (leftRelations (Submodule.span K (Set.range U)) ⊔ rightRelations S))
    (v : I → Y) (hv : (∑ j,U j ⊗ₜ[K] v j)∈rightRelations S ⊔ E) :
    ∀ i,v i∈S := by
  apply independent_tensor_coefficients_mem U hU S v
  have hl : (∑ j,U j ⊗ₜ[K] v j)∈leftRelations (Submodule.span K (Set.range U)) := by
    apply Submodule.sum_mem
    intro j _
    exact ⟨(⟨U j,Submodule.subset_span ⟨j,rfl⟩⟩ : Submodule.span K (Set.range U)) ⊗ₜ[K] v j,rfl⟩
  have hi : (∑ j,U j ⊗ₜ[K] v j)∈
      leftRelations (Submodule.span K (Set.range U)) ⊓ (rightRelations S ⊔ E) := ⟨hl,hv⟩
  rw [mixed_intersection_of_disjoint _ _ _ hE] at hi
  exact hi.2

end Froberg
