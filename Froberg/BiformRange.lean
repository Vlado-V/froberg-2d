module

public import Froberg.BiformExtension
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

@[expose] public section

/-! Exact image and quotient operations for the row-two construction. -/
noncomputable section
namespace Froberg
open Module TensorProduct
variable {K V ι : Type*} [Field K] [AddCommMonoid V] [Module K V] [Fintype ι]
variable {h m j e x y : ℕ}

theorem output_tmul_mem_biform_range (O : V →ₗ[K] Forms K h j)
    (o : ι → V) (f : ι → Forms K m e)
    (hconv : Function.Surjective (vectorFormFamilyMap (t := y) o f))
    (z : V ⊗[K] Forms K h x) (w : Forms K m (e+y)) :
    outputMultiplication O z ⊗ₜ[K] w ∈
      (biformFamilyMap (x := x) (y := y) (fun i => O (o i)) f).range := by
  let R := (biformFamilyMap (x := x) (y := y) (fun i => O (o i)) f).range
  have hs (v : V) (g : Forms K h x) : gradedMultiplication (O v) g ⊗ₜ[K] w ∈ R := by
    obtain ⟨c,hc⟩ := hconv (v ⊗ₜ[K] w)
    refine ⟨fun i => g ⊗ₜ[K] c i,?_⟩
    rw [biformFamilyMap_scalarCoefficients,hc]
    rfl
  induction z using TensorProduct.induction_on with
  | zero => simpa only [map_zero,zero_tmul] using Submodule.zero_mem R
  | tmul v g => exact hs v g
  | add z z' hz hz' => simpa only [map_add,add_tmul] using Submodule.add_mem R hz hz'

def homogeneousInclusion (A : Submodule K (Poly K h)) (hA : A ≤ Forms K h j) :
    A →ₗ[K] Forms K h j := Submodule.inclusion hA

theorem outputMultiplication_range (A : Submodule K (Poly K h)) (hA : A ≤ Forms K h j) :
    (outputMultiplication (x := x) (homogeneousInclusion A hA)).range =
      (A*Forms K h x).comap (Forms K h (j+x)).subtype := by
  have heq : (Forms K h (j+x)).subtype.comp
      (outputMultiplication (x := x) (homogeneousInclusion A hA)) =
        Submodule.mulMap A (Forms K h x) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    rfl
  rw [← Submodule.mulMap_range,← heq,LinearMap.range_comp,
    Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _)]

attribute [local instance] tensorGroup

/-- Every tensor over the actual output image belongs to the biform range. -/
theorem output_image_tensor_le_range (O : V →ₗ[K] Forms K h j)
    (o : ι → V) (f : ι → Forms K m e)
    (hconv : Function.Surjective (vectorFormFamilyMap (t := y) o f)) :
    (TensorProduct.map (outputMultiplication (x := x) O).range.subtype
      (LinearMap.id : Forms K m (e+y) →ₗ[K] _)).range ≤
      (biformFamilyMap (x := x) (y := y) (fun i => O (o i)) f).range := by
  rintro _ ⟨z,rfl⟩
  induction z using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | tmul u w =>
    obtain ⟨v,hv⟩ := u.property
    simpa only [TensorProduct.map_tmul,Submodule.subtype_apply,LinearMap.id_apply,hv] using
      output_tmul_mem_biform_range O o f hconv v w
  | add u v hu hv => simpa only [map_add] using Submodule.add_mem _ hu hv

section Coproduct
variable {E T Q Z : Type*} [AddCommGroup E] [Module K E]
  [AddCommGroup T] [Module K T] [AddCommGroup Q] [Module K Q]
  [AddCommGroup Z] [Module K Z]

theorem coprod_surjective_of_quotient (F : E →ₗ[K] T) (G : Z →ₗ[K] T) (π : T →ₗ[K] Q)
    (hker : π.ker ≤ F.range) (hG : Function.Surjective (π.comp G)) :
    Function.Surjective (F.coprod G) := by
  intro t
  obtain ⟨z,hz⟩ := hG (π t)
  have hk : t-G z ∈ π.ker := by
    change π (t-G z)=0
    rw [map_sub,show π (G z)=π t from hz,sub_self]
  obtain ⟨e,he⟩ := hker hk
  exact ⟨(e,z),by simpa only [LinearMap.coprod_apply,he,sub_add_cancel]⟩
end Coproduct

end Froberg
