module

public import Froberg.MixedTensorExactness

@[expose] public section

/-! Injectivity of the projected two-family map excludes all unintended
intersections with the actual tensor relation spaces. -/
noncomputable section
namespace Froberg
open Module TensorProduct Quartic.SplitTensor
variable {K A B V W : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem disjoint_range_of_projected_coprod (pi : V →ₗ[K] W)
    (f : A →ₗ[K] V) (g : B →ₗ[K] W) (S T : Submodule K V)
    (hS : S≤pi.ker) (hT : T.map pi≤g.range)
    (hinj : Function.Injective ((pi.comp f).coprod g)) :
    Disjoint f.range (S ⊔ T) := by
  apply disjoint_iff_inf_le.mpr
  rintro v ⟨⟨a,ha⟩,hv⟩
  obtain ⟨s,hs,t,ht,hst⟩ := Submodule.mem_sup.mp hv
  obtain ⟨b,hb⟩ := hT ⟨t,ht,rfl⟩
  have hpa : pi (f a)=g b := by
    rw [ha,←hst,map_add,show pi s=0 from hS hs,zero_add,hb]
  have hz : ((pi.comp f).coprod g) (a,-b)=0 := by
    simp only [LinearMap.coprod_apply,LinearMap.comp_apply,map_neg,hpa,add_neg_cancel]
  have he : (a,-b)=(0,0) := hinj (hz.trans (map_zero _).symm)
  have ha0 : a=0 := congrArg Prod.fst he
  exact (Submodule.mem_bot K).mpr (by rw [←ha,ha0,map_zero])

section Tensor
variable {X Y Z I : Type*}
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z] [Fintype I]
local instance relationSourceGroup : AddCommGroup (X ⊗[K] Y) := Module.addCommMonoidToAddCommGroup K
local instance relationTargetGroup : AddCommGroup (Z ⊗[K] Y) := Module.addCommMonoidToAddCommGroup K

theorem tensor_projected_relations_disjoint (P : X →ₗ[K] Z)
    (f : A →ₗ[K] (X ⊗[K] Y)) (Q : I → Y)
    (hinj : Function.Injective
      (((TensorProduct.map P (LinearMap.id : Y →ₗ[K] Y)).comp f).coprod
        (sumTensorRight (X := Z) Q))) :
    Disjoint f.range (leftRelations P.ker ⊔ rightRelations (Submodule.span K (Set.range Q))) := by
  let pi := TensorProduct.map P (LinearMap.id : Y →ₗ[K] Y)
  apply disjoint_range_of_projected_coprod pi f (sumTensorRight (X := Z) Q)
    (leftRelations P.ker) (rightRelations (Submodule.span K (Set.range Q))) _ _ hinj
  · rintro _ ⟨u,rfl⟩
    have he : pi.comp (TensorProduct.map P.ker.subtype (LinearMap.id : Y →ₗ[K] Y))=0 := by
      ext x y
      change P x.val ⊗ₜ[K] y=0
      rw [show P x.val=0 from x.property,zero_tmul]
    exact LinearMap.congr_fun he u
  · rw [←sumTensorRight_range]
    rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
    refine ⟨fun i => P (v i),?_⟩
    simp [pi,sumTensorRight_apply]

end Tensor
end Froberg
