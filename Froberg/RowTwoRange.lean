import Froberg.BiformRegrade

/-! Row two is filled by a linear-layer kernel and a quadratic-layer quotient.
All maps are the literal homogeneous polynomial multiplication maps. -/
noncomputable section
namespace Froberg
open TensorProduct Module
variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
variable {h m s e y : ℕ}
attribute [local instance] tensorGroup

theorem row_two_coprod_surjective
    (A : Submodule K (Poly K h)) (hA : A ≤ Forms K h 1)
    (o : ι → A) (f : ι → Forms K m s)
    (hF : Function.Surjective (vectorFormFamilyMap (t := s) o f))
    (O : κ → Forms K h 2) (g : κ → Forms K m e) (he : e+y=s+s)
    (hG : Function.Surjective (vectorFormFamilyMap (t := y)
      (fun i => (endpointProducts K h 1 A).mkQ (O i)) g)) :
    Function.Surjective ((biformFamilyMap (x := 1) (y := s)
      (fun i => homogeneousInclusion A hA (o i)) f).coprod
        (vectorFormFamilyToDegree he O g)) := by
  let U := endpointProducts K h 1 A
  letI : AddCommGroup ((Forms K h 2 ⧸ U) ⊗[K] Forms K m (s+s)) :=
    Module.addCommMonoidToAddCommGroup K
  let π := TensorProduct.map U.mkQ (LinearMap.id : Forms K m (s+s) →ₗ[K] _)
  apply coprod_surjective_of_quotient _ _ π
  · have hrange : (outputMultiplication (x := 1) (homogeneousInclusion A hA)).range = U :=
      outputMultiplication_range A hA
    have himage := output_image_tensor_le_range (x := 1) (y := s) (homogeneousInclusion A hA) o f hF
    rw [hrange] at himage
    have hker : π.ker = (TensorProduct.map U.subtype
        (LinearMap.id : Forms K m (s+s) →ₗ[K] _)).range :=
      rTensor_mkQ (Forms K m (s+s)) U
    rw [hker]
    exact himage
  · change Function.Surjective ((TensorProduct.map U.mkQ (LinearMap.id : Forms K m (s+s) →ₗ[K] _)).comp _)
    rw [vectorFormFamilyToDegree_project]
    exact vectorFormFamilyToDegree_surjective he _ g hG

end Froberg
