import Froberg.ConvolutionExactCount

/-! Actual multiplication of biform generators and transport of convolution
surjectivity through an output multiplication map. -/
noncomputable section
namespace Froberg
open TensorProduct
variable {K V ι : Type*} [Field K] [AddCommMonoid V] [Module K V] [Fintype ι]
variable {h m j e x y : ℕ}

def biformFamilyMap (o : ι → Forms K h j) (f : ι → Forms K m e) :
    (ι → Forms K h x ⊗[K] Forms K m y) →ₗ[K]
      Forms K h (j+x) ⊗[K] Forms K m (e+y) :=
  ∑ i, (TensorProduct.map (gradedMultiplication (o i)) (gradedMultiplication (f i))).comp
    (LinearMap.proj i)

@[simp] theorem biformFamilyMap_apply (o : ι → Forms K h j) (f : ι → Forms K m e)
    (c : ι → Forms K h x ⊗[K] Forms K m y) :
    biformFamilyMap o f c = ∑ i, TensorProduct.map
      (gradedMultiplication (o i)) (gradedMultiplication (f i)) (c i) := by
  simp [biformFamilyMap]

def outputMultiplication (O : V →ₗ[K] Forms K h j) :
    V ⊗[K] Forms K h x →ₗ[K] Forms K h (j+x) :=
  TensorProduct.lift (gradedMultiplication.comp O)

@[simp] theorem outputMultiplication_tmul (O : V →ₗ[K] Forms K h j)
    (v : V) (g : Forms K h x) :
    outputMultiplication O (v ⊗ₜ[K] g) = gradedMultiplication (O v) g := rfl

theorem biformFamilyMap_scalarCoefficients (O : V →ₗ[K] Forms K h j)
    (o : ι → V) (f : ι → Forms K m e) (g : Forms K h x) (c : ι → Forms K m y) :
    biformFamilyMap (fun i => O (o i)) f (fun i => g ⊗ₜ[K] c i) =
      TensorProduct.map ((gradedMultiplication.flip g).comp O) LinearMap.id
        (vectorFormFamilyMap o f c) := by
  simp only [biformFamilyMap_apply,vectorFormFamilyMap_apply,map_sum,TensorProduct.map_tmul,
    LinearMap.comp_apply,LinearMap.id_apply,LinearMap.flip_apply]

/-- Once the chosen output directions generate the desired X-degree,
convolution fills the entire corresponding bidegree. -/
theorem biformFamilyMap_surjective_of_output (O : V →ₗ[K] Forms K h j)
    (hO : Function.Surjective (outputMultiplication (x := x) O))
    (o : ι → V) (f : ι → Forms K m e)
    (hconv : Function.Surjective (vectorFormFamilyMap (t := y) o f)) :
    Function.Surjective (biformFamilyMap (x := x) (y := y) (fun i => O (o i)) f) := by
  let R := (biformFamilyMap (x := x) (y := y) (fun i => O (o i)) f).range
  have hsingle (v : V) (g : Forms K h x) (w : Forms K m (e+y)) :
      gradedMultiplication (O v) g ⊗ₜ[K] w ∈ R := by
    obtain ⟨c,hc⟩ := hconv (v ⊗ₜ[K] w)
    refine ⟨fun i => g ⊗ₜ[K] c i, ?_⟩
    rw [biformFamilyMap_scalarCoefficients,hc]
    rfl
  have hfull (z : V ⊗[K] Forms K h x) (w : Forms K m (e+y)) :
      outputMultiplication O z ⊗ₜ[K] w ∈ R := by
    induction z using TensorProduct.induction_on with
    | zero => simpa only [map_zero,zero_tmul] using Submodule.zero_mem R
    | tmul v g => exact hsingle v g w
    | add z z' hz hz' => simpa only [map_add,add_tmul] using Submodule.add_mem R hz hz'
  intro z
  change z ∈ R
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem R
  | tmul g w =>
    obtain ⟨u,rfl⟩ := hO g
    exact hfull u w
  | add z z' hz hz' => exact Submodule.add_mem R hz hz'

end Froberg
