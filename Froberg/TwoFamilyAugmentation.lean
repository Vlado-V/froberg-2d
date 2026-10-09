module

public import Froberg.ScalarAugmentation
public import Froberg.TwoFamilyIntrinsic

@[expose] public section

/-! Extracting an auxiliary scalar family from a successful augmented
mixed multiplication map gives actual quotient growth. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module
variable {K P₁ P₂ V₁ V₂ W : Type*} [Field K]
  [AddCommGroup P₁] [Module K P₁] [FiniteDimensional K P₁]
  [AddCommGroup P₂] [Module K P₂] [FiniteDimensional K P₂]
  [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
  [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {q₁ q₂ t : ℕ}

theorem twoFamily_append_coprod_injective
    (mu₁ : P₁ →ₗ[K] V₁ →ₗ[K] W) (mu₂ : P₂ →ₗ[K] V₂ →ₗ[K] W)
    (F : Fin q₁ → P₁) (Q : Fin q₂ → P₂) (A : Fin t → P₂)
    (h : Function.Injective (twoFamilyMultiplication mu₁ mu₂ (F,Fin.append Q A))) :
    Function.Injective ((twoFamilyMultiplication mu₁ mu₂ (F,Q)).coprod
      (BilinearScalarFamily.multiplication mu₂ A)) := by
  exact scalar_append_coprod_injective (BilinearScalarFamily.multiplication mu₁ F) mu₂ Q A h

/-- The auxiliary forms are witnesses for a uniform shadow estimate and do
not change the old generator count or its actual quotient. -/
theorem twoFamily_augmented_quotient_growth
    (mu₁ : P₁ →ₗ[K] V₁ →ₗ[K] W) (mu₂ : P₂ →ₗ[K] V₂ →ₗ[K] W)
    (F : Fin q₁ → P₁) (Q : Fin q₂ → P₂) (A : Fin t → P₂)
    (h : Function.Injective (twoFamilyMultiplication mu₁ mu₂ (F,Fin.append Q A)))
    (L : Submodule K V₂) :
    t*finrank K L≤finrank K (Quartic.BilinearImage.image
      (scalarModulo (twoFamilyMultiplication mu₁ mu₂ (F,Q)) mu₂) L) :=
  additional_scalar_quotient_growth _ mu₂ A
    (twoFamily_append_coprod_injective mu₁ mu₂ F Q A h) L

end Froberg
