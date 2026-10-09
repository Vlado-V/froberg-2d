module

public import Froberg.BiformRegrade

@[expose] public section

/-! The restricted scalar multipliers in row two embed in the full biform
coefficient space. Thus the witnesses are points of the full parameter space. -/
noncomputable section
namespace Froberg
open TensorProduct Module
variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
variable {h m s e y t : ℕ}
attribute [local instance] tensorGroup

def constantOneForm (K : Type*) [Field K] (h : ℕ) : Forms K h 0 :=
  ⟨1,MvPolynomial.isHomogeneous_one _ _⟩

def biformTensorFamilyToDegree {j x : ℕ} (he : e+y=t) :
    (ι → Forms K h j ⊗[K] Forms K m e) →ₗ[K]
    ((ι → Forms K h x ⊗[K] Forms K m y) →ₗ[K] Forms K h (j+x) ⊗[K] Forms K m t) :=
  (LinearMap.llcomp K _ _ _ (TensorProduct.map LinearMap.id (formsDegreeEquiv he).toLinearMap)).comp
    biformTensorFamilyMap

theorem biform_zero_coefficients (o : κ → Forms K h 2) (g : κ → Forms K m e)
    (c : κ → Forms K m y) :
    biformFamilyMap (x := 0) o g (fun i => constantOneForm K h ⊗ₜ[K] c i) =
      vectorFormFamilyMap o g c := by
  have ho (i : κ) : gradedMultiplication (o i) (constantOneForm K h) = o i := by
    apply Subtype.ext
    exact mul_one _
  simp only [biformFamilyMap_apply,TensorProduct.map_tmul,vectorFormFamilyMap_apply,ho]

theorem row_two_full_surjective
    (o : ι → Forms K h 1) (f : ι → Forms K m s)
    (O : κ → Forms K h 2) (g : κ → Forms K m e) (he : e+y=s+s)
    (hs : Function.Surjective ((biformFamilyMap (x := 1) (y := s) o f).coprod
      (vectorFormFamilyToDegree he O g))) :
    Function.Surjective ((biformTensorFamilyMap (x := 1) (y := s) (fun i => o i ⊗ₜ[K] f i)).coprod
      (biformTensorFamilyToDegree (x := 0) he (fun i => O i ⊗ₜ[K] g i))) := by
  intro z
  obtain ⟨⟨a,b⟩,hab⟩ := hs z
  refine ⟨(a,fun i => constantOneForm K h ⊗ₜ[K] b i),?_⟩
  simpa only [LinearMap.coprod_apply,biformTensorFamilyMap_pure,biformTensorFamilyToDegree,
    LinearMap.comp_apply,LinearMap.llcomp_apply,vectorFormFamilyToDegree,biform_zero_coefficients] using hab

end Froberg
