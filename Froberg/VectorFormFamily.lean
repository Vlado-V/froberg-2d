import Froberg.Prefix
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! Actual multiplication of finitely many vector-valued forms. -/
noncomputable section
namespace Froberg
open TensorProduct
variable {K W ι : Type*} [Field K] [AddCommMonoid W] [Module K W]
variable [Fintype ι] {m e t : ℕ}

/-- The generators are the literal tensors `o i ⊗ f i`. -/
def vectorFormFamilyMap (o : ι → W) (f : ι → Forms K m e) :
    (ι → Forms K m t) →ₗ[K] W ⊗[K] Forms K m (e + t) :=
  ∑ i, ((TensorProduct.mk K W (Forms K m (e + t))) (o i)).comp
    ((gradedMultiplication (f i)).comp (LinearMap.proj i))

@[simp] theorem vectorFormFamilyMap_apply (o : ι → W) (f : ι → Forms K m e)
    (g : ι → Forms K m t) :
    vectorFormFamilyMap o f g = ∑ i, o i ⊗ₜ[K] gradedMultiplication (f i) (g i) := by
  simp [vectorFormFamilyMap]

@[simp] theorem vectorFormFamilyMap_single [DecidableEq ι] (o : ι → W)
    (f : ι → Forms K m e) (i : ι) (g : Forms K m t) :
    vectorFormFamilyMap o f (Pi.single i g) = o i ⊗ₜ[K] gradedMultiplication (f i) g := by
  rw [vectorFormFamilyMap_apply, Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Pi.single_apply, hji]
  · simp

theorem vectorFormFamilyMap_single_mem (o : ι → W) (f : ι → Forms K m e)
    (i : ι) (g : Forms K m t) :
    o i ⊗ₜ[K] gradedMultiplication (f i) g ∈ (vectorFormFamilyMap o f).range := by
  classical
  exact ⟨Pi.single i g, vectorFormFamilyMap_single o f i g⟩

variable {Z : Type*} [AddCommMonoid Z] [Module K Z]

theorem vectorFormFamilyMap_project (P : W →ₗ[K] Z) (o : ι → W)
    (f : ι → Forms K m e) (g : ι → Forms K m t) :
    TensorProduct.map P LinearMap.id (vectorFormFamilyMap o f g) =
      vectorFormFamilyMap (fun i => P (o i)) f g := by
  simp only [vectorFormFamilyMap_apply, map_sum, TensorProduct.map_tmul, LinearMap.id_apply]

theorem vectorFormFamilyMap_surjective_project (P : W →ₗ[K] Z)
    (hP : Function.Surjective P) (o : ι → W) (f : ι → Forms K m e)
    (hf : Function.Surjective (vectorFormFamilyMap (t := t) o f)) :
    Function.Surjective (vectorFormFamilyMap (t := t) (fun i => P (o i)) f) := by
  have hT : Function.Surjective (TensorProduct.map P (LinearMap.id : Forms K m (e+t) →ₗ[K] _)) :=
    TensorProduct.map_surjective hP Function.surjective_id
  intro z
  obtain ⟨w, hw⟩ := hT z
  obtain ⟨g, hg⟩ := hf w
  refine ⟨g, ?_⟩
  rw [← vectorFormFamilyMap_project P o f, hg, hw]

end Froberg
