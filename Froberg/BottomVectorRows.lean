import Froberg.LinearOutputTensor
import Froberg.OddBackgroundRowProjection
import Froberg.ScalarDoubleQuotient

/-! The actual bottom tensor relation map is the vector-valued scalar
model, including both the old vector relations and the scalar family. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct Quartic VectorMultiplicationCoordinates
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}

def bottomOutputTargetEquiv (hd : 1 ≤ d) :
    Rows K h m ((d-1)+d) ≃ₗ[K] (Forms K h 1 ⊗[K] Forms K m (2*d-1)) :=
  linearOutputTensorEquiv.trans (biformDegreeTransport rfl (by omega))

@[simp] theorem sumBiformMap_bottomOutputTarget (hd : 1 ≤ d)
    (v : Rows K h m ((d-1)+d)) :
    sumBiformMap (bottomOutputTargetEquiv hd v)=sumBiformMap (linearOutputTensorEquiv v) :=
  sumBiformMap_degreeTransport _ _ _

def bottomLinearCoefficientEquiv (hd : 1 ≤ d) :
    Forms K m d ≃ₗ[K] (Forms K h (1-1) ⊗[K] Forms K m (d-1+1)) :=
  (scalarBiformEquiv (h := h)).trans (biformDegreeTransport rfl (by omega))

theorem sumBiformMap_scalarBiform (p : Forms K m d) :
    sumBiformMap (scalarBiformEquiv (h := h) p)=rename Sum.inr p.val := by
  rw [scalarBiformEquiv_apply,sumBiformMap_tmul]
  change rename Sum.inl (C (1 : K))*rename Sum.inr p.val=_
  simp

@[simp] theorem sumBiformMap_bottomLinearCoefficient (hd : 1 ≤ d)
    (p : Forms K m d) :
    sumBiformMap (bottomLinearCoefficientEquiv (h := h) hd p)=rename Sum.inr p.val := by
  rw [bottomLinearCoefficientEquiv,LinearEquiv.trans_apply,sumBiformMap_degreeTransport,
    sumBiformMap_scalarBiform]

theorem bottom_vector_linear_action (hd : 1 ≤ d) (g : Rows K h m (d-1)) (a : Forms K m d) :
    oddRowLinearAction (b := 1) (by decide) hd (linearOutputTensorEquiv g)
      (bottomLinearCoefficientEquiv hd a)=bottomOutputTargetEquiv hd (multiplication a g) := by
  apply sumBiformMap_injective
  rw [oddRowLinearAction,sumBiformMap_action,sumBiformMap_bottomLinearCoefficient,
    sumBiformMap_bottomOutputTarget,linearOutput_scalar_product,mul_comm]

theorem bottom_vector_scalar_action (hd : 1 ≤ d) (p : Forms K m d) (v : Rows K h m (d-1)) :
    oddRowScalarAction (b := 1) hd (scalarBiformEquiv (h := h) p)
      (linearOutputTensorEquiv v)=bottomOutputTargetEquiv hd (multiplication p v) := by
  apply sumBiformMap_injective
  rw [oddRowScalarAction,sumBiformMap_action,sumBiformMap_scalarBiform,
    sumBiformMap_bottomOutputTarget,linearOutput_scalar_product]

def bottomVectorRow (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1)) :
    ((Fin f → Forms K m d) × (Fin q → Rows K h m (d-1))) →ₗ[K] Rows K h m ((d-1)+d) :=
  (BilinearImage.tupleMap multiplication g).coprod (BilinearScalarFamily.multiplication multiplication Q)

def bottomRowCoefficients (hd : 1 ≤ d) :
    ((Fin f → Forms K m d) × (Fin q → Rows K h m (d-1))) ≃ₗ[K]
      ((Fin f → Forms K h (1-1) ⊗[K] Forms K m (d-1+1)) ×
        (Fin q → Forms K h 1 ⊗[K] Forms K m (d-1))) :=
  LinearEquiv.prodCongr (LinearEquiv.piCongrRight (fun _ => bottomLinearCoefficientEquiv hd))
    (LinearEquiv.piCongrRight (fun _ => linearOutputTensorEquiv))

set_option backward.isDefEq.respectTransparency true in
 theorem bottomRow_map_comparison (hd : 1 ≤ d)
    (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1)) :
    (oddTensorRowMap (b := 1) (by decide) hd (fun i => scalarBiformEquiv (h := h) (Q i))
      (fun i => linearOutputTensorEquiv (g i))).comp
        (bottomRowCoefficients (K := K) (h := h) (m := m) (d := d) (q := q) (f := f) hd).toLinearMap=
      (bottomOutputTargetEquiv hd).toLinearMap.comp (bottomVectorRow Q g) := by
  apply LinearMap.ext
  rintro ⟨a,v⟩
  simp only [LinearMap.comp_apply,oddTensorRowMap,twoFamilyMultiplication,LinearMap.coprod_apply,
    BilinearScalarFamily.multiplication_apply,bottomRowCoefficients,LinearEquiv.coe_coe,
    LinearEquiv.prodCongr_apply,LinearEquiv.piCongrRight_apply,bottom_vector_linear_action,
    bottom_vector_scalar_action,bottomVectorRow,BilinearImage.tupleMap_apply,map_add,map_sum]

 theorem bottomRow_range_comparison (hd : 1 ≤ d)
    (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1)) :
    (oddTensorRowMap (b := 1) (by decide) hd (fun i => scalarBiformEquiv (h := h) (Q i))
      (fun i => linearOutputTensorEquiv (g i))).range=
      (BilinearImage.image multiplication (Submodule.span K (Set.range g)) ⊔
        (BilinearScalarFamily.multiplication multiplication Q).range).map
          (bottomOutputTargetEquiv hd).toLinearMap := by
  have he := congrArg LinearMap.range (bottomRow_map_comparison hd Q g)
  rw [LinearMap.range_comp,LinearMap.range_eq_top.mpr (bottomRowCoefficients hd).surjective,
    Submodule.map_top,LinearMap.range_comp] at he
  rw [bottomVectorRow,LinearMap.range_coprod,BilinearImage.range_tupleMap] at he
  exact he

end Froberg
