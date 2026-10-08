import Froberg.TensorScalarGrowth
import Froberg.BilinearScalarFamily
import Quartic.SplitTensor

/-! Compatibility of the actual tensor products and family maps with a
projection of the first tensor factor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module TensorProduct Quartic.SplitTensor
attribute [local instance] tensorFormGroup
variable {K B V W Z : Type*} [Field K]
  [AddCommGroup B] [Module K B] [FiniteDimensional K B]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]
variable {m d e q : ℕ}

theorem bilinear_family_postcompose (mu : B →ₗ[K] V →ₗ[K] W)
    (P : W →ₗ[K] Z) (F : Fin q → B) :
    BilinearScalarFamily.multiplication (mu.compr₂ₛₗ P) F=
      P.comp (BilinearScalarFamily.multiplication mu F) := by
  apply LinearMap.ext
  intro x
  simp [BilinearScalarFamily.multiplication_apply]

theorem tensorFormProduct_postcompose (mu : B →ₗ[K] V →ₗ[K] W) (P : W →ₗ[K] Z) :
    tensorFormProduct (m := m) (d := d) (e := e) (mu.compr₂ₛₗ P)=
      (tensorFormProduct mu).compr₂ₛₗ
        (TensorProduct.map P (LinearMap.id : Forms K m (e+d) →ₗ[K] Forms K m (e+d))) := by
  ext b f v g
  rfl

theorem tensorScalarFamily_eq_sumTensorRight {Y : Type*}
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y] (Q : Fin q → Y) :
    BilinearScalarFamily.multiplication (tensorScalarProduct (K := K) (V := V) (P := Y)) Q=
      sumTensorRight (K := K) (X := V) Q := by
  apply LinearMap.ext
  intro x
  simp only [BilinearScalarFamily.multiplication_apply,sumTensorRight_apply]
  rfl

end Froberg
