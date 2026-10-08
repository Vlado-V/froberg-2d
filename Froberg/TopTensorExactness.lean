import Froberg.ProjectedTopOpen
import Froberg.TensorPostcomposition
import Froberg.ProjectedRelationSeparation

/-! The polynomial top-row map satisfies the actual tensor separation
hypothesis of the C.10 exact sequence. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module TensorProduct Quartic Quartic.SplitTensor
attribute [local instance] tensorFormGroup
variable {K : Type*} [Field K] [Infinite K] {h m e b qF qS : ℕ}

def rawTopFamily (F : Fin qF → Forms K h 1 ⊗[K] Forms K m e) :
    (Fin qF → Forms K h e ⊗[K] Forms K m 1) →ₗ[K]
      (Forms K h (1+e) ⊗[K] Forms K m (1+e)) :=
  BilinearScalarFamily.multiplication
    (tensorFormProduct (d := e) (e := 1) (gradedMultiplication (K := K) (n := h) (d := 1) (e := e))) F

theorem projectedTopFamily_eq (P : Forms K h (1+e) →ₗ[K] (Fin b → K))
    (F : Fin qF → Forms K h 1 ⊗[K] Forms K m e) :
    BilinearScalarFamily.multiplication (K := K)
      (F := Forms K h 1 ⊗[K] Forms K m e)
      (V := Forms K h e ⊗[K] Forms K m 1)
      (W := (Fin b → K) ⊗[K] Forms K m (1+e))
      (projectedTopLinearAction (m := m) P) F=
      (TensorProduct.map P (LinearMap.id : Forms K m (1+e) →ₗ[K] _)).comp (rawTopFamily F) := by
  rw [projectedTopLinearAction,tensorFormProduct_postcompose]
  apply LinearMap.ext
  intro x
  simp only [rawTopFamily,BilinearScalarFamily.multiplication_apply,
    LinearMap.comp_apply,LinearMap.compr₂ₛₗ_apply,map_sum]

theorem top_tensor_separation (P : Forms K h (1+e) →ₗ[K] (Fin b → K))
    (F : Fin qF → Forms K h 1 ⊗[K] Forms K m e) (Q : Fin qS → Forms K m (1+e))
    (hinj : Function.Injective (twoFamilyMultiplication (K := K)
      (V₁ := Forms K h e ⊗[K] Forms K m 1) (V₂ := Fin b → K)
      (projectedTopLinearAction (m := m) P)
      (tensorScalarProduct (K := K) (V := Fin b → K) (P := Forms K m (1+e))) (F,Q))) :
    Disjoint (rawTopFamily F).range
      (leftRelations P.ker ⊔ rightRelations (Submodule.span K (Set.range Q))) := by
  apply tensor_projected_relations_disjoint (K := K)
    (X := Forms K h (1+e)) (Y := Forms K m (1+e)) (Z := Fin b → K)
    (A := Fin qF → Forms K h e ⊗[K] Forms K m 1) P (rawTopFamily F) Q
  have hQ : BilinearScalarFamily.multiplication (K := K)
      (F := Forms K m (1+e)) (V := Fin b → K) (W := (Fin b → K) ⊗[K] Forms K m (1+e))
      (tensorScalarProduct (K := K) (V := Fin b → K) (P := Forms K m (1+e))) Q=
      sumTensorRight (K := K) (X := Fin b → K) Q := by
    apply LinearMap.ext
    intro x
    simp only [BilinearScalarFamily.multiplication_apply,sumTensorRight_apply]
    rfl
  simpa only [twoFamilyMultiplication,projectedTopFamily_eq,hQ] using hinj

end Froberg
