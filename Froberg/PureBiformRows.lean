module

public import Froberg.PureCutoffPropagation
public import Froberg.BiformFullRow

@[expose] public section

/-! A basis of a full pure-X product supplies the actual biform rows used
above the cutoff, in the same tuple multiplication API as lower rows. -/
noncomputable section
namespace Froberg
open Module TensorProduct
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
variable {h m d x y : ℕ}
attribute [local instance] tensorGroup

theorem vectorFormFamilyMap_one_surjective_of_span (v : ι → V)
    (hv : Submodule.span K (Set.range v)=⊤) :
    Function.Surjective (vectorFormFamilyMap (t := y) v (fun _ : ι => constantOneForm K m)) := by
  classical
  have hone (f : Forms K m (0+y)) :
      gradedMultiplication (constantOneForm K m) (formsDegreeEquiv (Nat.zero_add y) f)=f := by
    apply Subtype.ext
    exact one_mul f.val
  intro z
  change z∈(vectorFormFamilyMap (t := y) v (fun _ : ι => constantOneForm K m)).range
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add u w hu hw => exact Submodule.add_mem _ hu hw
  | tmul w f =>
    have hw : w∈Submodule.span K (Set.range v) := by rw [hv];trivial
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hw
    refine ⟨fun i => c i • formsDegreeEquiv (Nat.zero_add y) f,?_⟩
    rw [vectorFormFamilyMap_apply]
    simp only [map_smul,hone,tmul_smul,smul_tmul']
    rw [←sum_tmul,hc]

theorem vectorFormFamilyMap_one_surjective (b : Basis ι K V) :
    Function.Surjective (vectorFormFamilyMap (t := y) b (fun _ : ι => constantOneForm K m)) :=
  vectorFormFamilyMap_one_surjective_of_span b b.span_eq

theorem pure_biform_family_surjective (U : Submodule K (Poly K h))
    (hU : U≤Forms K h d) (u : ι → U) (hu : Submodule.span K (Set.range u)=⊤)
    (hfull : U*Forms K h x=Forms K h (d+x)) :
    Function.Surjective (biformFamilyMap (x := x) (y := y)
      (fun i => homogeneousInclusion U hU (u i)) (fun _ => constantOneForm K m)) := by
  apply biformFamilyMap_surjective_of_output (homogeneousInclusion U hU)
  · apply LinearMap.range_eq_top.mp
    rw [outputMultiplication_range,hfull]
    exact Submodule.comap_subtype_self _
  · exact vectorFormFamilyMap_one_surjective_of_span u hu

theorem pure_biform_basis_surjective (U : Submodule K (Poly K h))
    (hU : U≤Forms K h d) (basis : Basis ι K U)
    (hfull : U*Forms K h x=Forms K h (d+x)) :
    Function.Surjective (biformFamilyMap (x := x) (y := y)
      (fun i => homogeneousInclusion U hU (basis i)) (fun _ => constantOneForm K m)) := by
  apply biformFamilyMap_surjective_of_output (homogeneousInclusion U hU)
  · apply LinearMap.range_eq_top.mp
    rw [outputMultiplication_range,hfull]
    exact Submodule.comap_subtype_self _
  · exact vectorFormFamilyMap_one_surjective basis

end Froberg
