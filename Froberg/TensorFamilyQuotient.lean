module

public import Froberg.TensorQuotientCoordinates
public import Froberg.BilinearPostcompose

@[expose] public section

/-! Canonical scalar action in the tensor quotient by the actual two
families. Its formula on every lifted vector is the original tensor product. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg
attribute [local instance] tensorQuotientGroup
open Module TensorProduct Quartic Quartic.SplitTensor
variable {K X Y Z A I : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z] [AddCommGroup A] [Module K A] [Fintype I]

def projectedTensorFamily (P : X →ₗ[K] Z) (f : A →ₗ[K] X ⊗[K] Y) (Q : I → Y) :=
  ((TensorProduct.map P (LinearMap.id : Y →ₗ[K] Y)).comp f).coprod
    (sumTensorRight (K := K) (X := Z) Q)

def tensorFamilyRelations (P : X →ₗ[K] Z) (f : A →ₗ[K] X ⊗[K] Y) (Q : I → Y) :=
  leftRelations P.ker ⊔ (rightRelations (Submodule.span K (Set.range Q)) ⊔ f.range)

theorem projectedTensorFamily_range (P : X →ₗ[K] Z)
    (f : A →ₗ[K] X ⊗[K] Y) (Q : I → Y) :
    (projectedTensorFamily P f Q).range=
      rightRelations (Submodule.span K (Set.range Q)) ⊔
        f.range.map (TensorProduct.map P (LinearMap.id : Y →ₗ[K] Y)) := by
  rw [projectedTensorFamily,LinearMap.range_coprod,LinearMap.range_comp,sumTensorRight_range]
  exact sup_comm _ _

def tensorFamilyQuotientEquiv (P : X →ₗ[K] Z) (hP : Function.Surjective P)
    (f : A →ₗ[K] X ⊗[K] Y) (Q : I → Y) :
    ((X ⊗[K] Y) ⧸ tensorFamilyRelations P f Q) ≃ₗ[K]
      ((Z ⊗[K] Y) ⧸ (projectedTensorFamily P f Q).range) :=
  (tensorQuotientEquiv P hP (Submodule.span K (Set.range Q)) f.range).trans
    (Submodule.quotEquivOfEq _ _ (projectedTensorFamily_range P f Q).symm)

@[simp] theorem tensorFamilyQuotientEquiv_tmul (P : X →ₗ[K] Z) (hP : Function.Surjective P)
    (f : A →ₗ[K] X ⊗[K] Y) (Q : I → Y) (x : X) (y : Y) :
    tensorFamilyQuotientEquiv P hP f Q ((tensorFamilyRelations P f Q).mkQ (x ⊗ₜ[K] y))=
      (projectedTensorFamily P f Q).range.mkQ (P x ⊗ₜ[K] y) := by
  rfl

def projectedTensorScalarAction (P : X →ₗ[K] Z) (f : A →ₗ[K] X ⊗[K] Y) (Q : I → Y) :
    Y →ₗ[K] Z →ₗ[K] ((Z ⊗[K] Y) ⧸ (projectedTensorFamily P f Q).range) :=
  (TensorProduct.mk K Z Y).flip.compr₂ₛₗ (projectedTensorFamily P f Q).range.mkQ

def tensorFamilyScalarAction (P : X →ₗ[K] Z) (hP : Function.Surjective P)
    (f : A →ₗ[K] X ⊗[K] Y) (Q : I → Y) :
    Y →ₗ[K] Z →ₗ[K] ((X ⊗[K] Y) ⧸ tensorFamilyRelations P f Q) :=
  (projectedTensorScalarAction P f Q).compr₂ₛₗ
    (tensorFamilyQuotientEquiv P hP f Q).symm.toLinearMap

theorem tensorFamilyScalarAction_lift (P : X →ₗ[K] Z) (hP : Function.Surjective P)
    (f : A →ₗ[K] X ⊗[K] Y) (Q : I → Y) (x : X) (y : Y) :
    tensorFamilyScalarAction P hP f Q y (P x)=
      (tensorFamilyRelations P f Q).mkQ (x ⊗ₜ[K] y) := by
  apply (tensorFamilyQuotientEquiv P hP f Q).injective
  change (tensorFamilyQuotientEquiv P hP f Q)
    ((tensorFamilyQuotientEquiv P hP f Q).symm
      ((projectedTensorFamily P f Q).range.mkQ (P x ⊗ₜ[K] y)))=_
  rw [LinearEquiv.apply_symm_apply,tensorFamilyQuotientEquiv_tmul]

theorem tensorFamilyScalarAction_finrank (P : X →ₗ[K] Z) (hP : Function.Surjective P)
    (f : A →ₗ[K] X ⊗[K] Y) (Q : I → Y) (L : Submodule K Z) :
    finrank K (BilinearImage.image (tensorFamilyScalarAction P hP f Q) L)=
      finrank K (BilinearImage.image (projectedTensorScalarAction P f Q) L) := by
  rw [tensorFamilyScalarAction,bilinearImage_postcompose]
  exact (tensorFamilyQuotientEquiv P hP f Q).symm.finrank_map_eq _

end Froberg
