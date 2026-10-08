import Froberg.TwoFamilyIntrinsicOpen
import Froberg.TwoFamilyAugmentation
import Froberg.FreezeParameters

/-! Uniform scalar-quotient growth on a genuine open in the old parameter
space, obtained by fixing a successful auxiliary scalar family. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Quartic
variable {K P₁ P₂ V₁ V₂ W : Type*} [Field K] [Infinite K]
  [AddCommGroup P₁] [Module K P₁] [FiniteDimensional K P₁]
  [AddCommGroup P₂] [Module K P₂] [FiniteDimensional K P₂]
  [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
  [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {q₁ q₂ t T : ℕ}

def appendScalarParameters :
    (((Fin q₁ → P₁) × (Fin q₂ → P₂)) × (Fin t → P₂)) →ₗ[K]
      ((Fin q₁ → P₁) × (Fin (q₂+t) → P₂)) where
  toFun p := (p.1.1,Fin.append p.1.2 p.2)
  map_add' p q := by
    apply Prod.ext
    · rfl
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
  map_smul' c p := by
    apply Prod.ext
    · rfl
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp

theorem appendScalarParameters_surjective : Function.Surjective
    (appendScalarParameters (K := K) (P₁ := P₁) (P₂ := P₂)
      (q₁ := q₁) (q₂ := q₂) (t := t)) := by
  intro p
  refine ⟨((p.1,fun i => p.2 (Fin.castAdd t i)),fun i => p.2 (Fin.natAdd q₂ i)),?_⟩
  apply Prod.ext
  · rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [appendScalarParameters]

theorem two_family_augmentation_open
    (mu₁ : P₁ →ₗ[K] V₁ →ₗ[K] W) (mu₂ : P₂ →ₗ[K] V₂ →ₗ[K] W)
    (ha₁ : 0<finrank K V₁) (ha₂ : 0<finrank K V₂)
    (h₁ : ∀ L : Submodule K V₁,
      T*finrank K L ≤ finrank K V₁*finrank K (BilinearImage.image mu₁ L))
    (h₂ : ∀ L : Submodule K V₂,
      T*finrank K L ≤ finrank K V₂*finrank K (BilinearImage.image mu₂ L))
    (hcount : (q₁+finrank K V₁)*finrank K V₁+
      (q₂+t+finrank K V₂)*finrank K V₂ ≤ T) :
    ∃ D : MvPolynomial (Fin (finrank K ((Fin q₁ → P₁) × (Fin q₂ → P₂)))) K,
      (∃ p : (Fin q₁ → P₁) × (Fin q₂ → P₂),
        eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p : (Fin q₁ → P₁) × (Fin q₂ → P₂),
        eval ((Module.finBasis K _).equivFun p) D≠0 →
        Function.Injective (twoFamilyMultiplication mu₁ mu₂ p) ∧
        ∀ L : Submodule K V₂,
          t*finrank K L≤finrank K (BilinearImage.image
            (scalarModulo (twoFamilyMultiplication mu₁ mu₂ p) mu₂) L) := by
  obtain ⟨D,hD,hgood⟩ := two_family_generic_of_natural_growth mu₁ mu₂ ha₁ ha₂ h₁ h₂ hcount
  obtain ⟨A,P,hP,hPA⟩ := principal_open_freeze_parameters
    (appendScalarParameters (K := K) (q₁ := q₁) (q₂ := q₂) (t := t))
    appendScalarParameters_surjective D hD
    (fun p => Function.Injective (twoFamilyMultiplication mu₁ mu₂ p)) hgood
  refine ⟨P,hP,?_⟩
  intro p hp
  have hi := twoFamily_append_coprod_injective mu₁ mu₂ p.1 p.2 A (hPA p hp)
  refine ⟨?_,fun L => twoFamily_augmented_quotient_growth mu₁ mu₂ p.1 p.2 A (hPA p hp) L⟩
  intro x y hxy
  have hh : (twoFamilyMultiplication mu₁ mu₂ p).coprod
      (BilinearScalarFamily.multiplication mu₂ A) (x,0)=
      (twoFamilyMultiplication mu₁ mu₂ p).coprod
      (BilinearScalarFamily.multiplication mu₂ A) (y,0) := by
    simpa only [LinearMap.coprod_apply,map_zero,add_zero] using hxy
  exact congrArg Prod.fst (hi hh)

end Froberg
