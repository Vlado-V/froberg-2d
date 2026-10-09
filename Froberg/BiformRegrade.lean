module

public import Froberg.BiformRange

@[expose] public section

/-! Degree identifications for literal homogeneous tensor multiplication. -/
noncomputable section
namespace Froberg
open TensorProduct
variable {K V Z ι : Type*} [Field K] [AddCommMonoid V] [Module K V]
  [AddCommMonoid Z] [Module K Z] [Fintype ι]
variable {n e y t : ℕ}

def formsDegreeEquiv {a b : ℕ} (hab : a=b) : Forms K n a ≃ₗ[K] Forms K n b :=
  LinearEquiv.ofEq _ _ (congrArg (Forms K n) hab)

@[simp] theorem formsDegreeEquiv_val {a b : ℕ} (hab : a=b) (f : Forms K n a) :
    (formsDegreeEquiv hab f : Forms K n b).val = f.val := by subst b; rfl

def vectorFormFamilyToDegree (he : e+y=t) (o : ι → V) (f : ι → Forms K n e) :
    (ι → Forms K n y) →ₗ[K] V ⊗[K] Forms K n t :=
  (TensorProduct.map LinearMap.id (formsDegreeEquiv he).toLinearMap).comp (vectorFormFamilyMap o f)

@[simp] theorem vectorFormFamilyToDegree_apply (he : e+y=t) (o : ι → V) (f : ι → Forms K n e)
    (c : ι → Forms K n y) :
    vectorFormFamilyToDegree he o f c =
      ∑ i, o i ⊗ₜ[K] formsDegreeEquiv he (gradedMultiplication (f i) (c i)) := by
  simp [vectorFormFamilyToDegree,vectorFormFamilyMap_apply]

theorem vectorFormFamilyToDegree_project (P : V →ₗ[K] Z) (he : e+y=t)
    (o : ι → V) (f : ι → Forms K n e) :
    (TensorProduct.map P (LinearMap.id : Forms K n t →ₗ[K] _)).comp
      (vectorFormFamilyToDegree he o f) = vectorFormFamilyToDegree he (fun i => P (o i)) f := by
  ext c
  simp only [LinearMap.comp_apply,vectorFormFamilyToDegree_apply,map_sum,TensorProduct.map_tmul,
    LinearMap.id_apply]

theorem vectorFormFamilyToDegree_surjective (he : e+y=t) (o : ι → V) (f : ι → Forms K n e)
    (hf : Function.Surjective (vectorFormFamilyMap (t := y) o f)) :
    Function.Surjective (vectorFormFamilyToDegree he o f) :=
  (TensorProduct.map_surjective Function.surjective_id (formsDegreeEquiv he).surjective).comp hf

end Froberg
