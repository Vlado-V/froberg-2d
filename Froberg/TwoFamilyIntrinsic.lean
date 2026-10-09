module

public import Froberg.BilinearScalarFamily
public import Froberg.TwoFamilyBudget

@[expose] public section

/-! Coordinate transport for two literal bilinear multiplication families. -/
noncomputable section
namespace Froberg
open Module Quartic
variable {K P₁ P₂ V₁ V₂ W : Type*} [Field K]
  [AddCommGroup P₁] [Module K P₁] [FiniteDimensional K P₁]
  [AddCommGroup P₂] [Module K P₂] [FiniteDimensional K P₂]
  [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
  [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {q₁ q₂ : ℕ}

/-- Sum of the two actual multiplication maps, with fixed generator families. -/
def twoFamilyMultiplication (mu₁ : P₁ →ₗ[K] V₁ →ₗ[K] W)
    (mu₂ : P₂ →ₗ[K] V₂ →ₗ[K] W) (p : (Fin q₁ → P₁) × (Fin q₂ → P₂)) :
    ((Fin q₁ → V₁) × (Fin q₂ → V₂)) →ₗ[K] W :=
  (BilinearScalarFamily.multiplication mu₁ p.1).coprod
    (BilinearScalarFamily.multiplication mu₂ p.2)

@[simp] theorem twoFamilyMultiplication_apply (mu₁ : P₁ →ₗ[K] V₁ →ₗ[K] W)
    (mu₂ : P₂ →ₗ[K] V₂ →ₗ[K] W) (p : (Fin q₁ → P₁) × (Fin q₂ → P₂))
    (x : (Fin q₁ → V₁) × (Fin q₂ → V₂)) :
    twoFamilyMultiplication mu₁ mu₂ p x =
      (∑ i, mu₁ (p.1 i) (x.1 i))+(∑ i, mu₂ (p.2 i) (x.2 i)) := by
  simp only [twoFamilyMultiplication,LinearMap.coprod_apply,
    BilinearScalarFamily.multiplication_apply]

theorem bilinearImage_compl₂ {P V V' W : Type*} [AddCommGroup P] [Module K P]
    [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    [AddCommGroup W] [Module K W]
    (mu : P →ₗ[K] V →ₗ[K] W) (e : V' →ₗ[K] V) (L : Submodule K V') :
    BilinearImage.image (mu.compl₂ e) L = BilinearImage.image mu (L.map e) := by
  unfold BilinearImage.image
  congr 1
  funext p
  rw [←Submodule.map_comp]
  rfl

/-- Choosing bases of the coefficient spaces preserves injectivity of the
actual sum of products; generator coordinates do not change. -/
theorem twoFamilyMultiplication_injective_of_coordinates {V₁' V₂' : Type*}
    [AddCommGroup V₁'] [Module K V₁'] [FiniteDimensional K V₁']
    [AddCommGroup V₂'] [Module K V₂'] [FiniteDimensional K V₂']
    (e₁ : V₁ ≃ₗ[K] V₁') (e₂ : V₂ ≃ₗ[K] V₂')
    (mu₁ : P₁ →ₗ[K] V₁ →ₗ[K] W) (mu₂ : P₂ →ₗ[K] V₂ →ₗ[K] W)
    (p : (Fin q₁ → P₁) × (Fin q₂ → P₂))
    (hp : Function.Injective (twoFamilyMultiplication (mu₁.compl₂ e₁.symm.toLinearMap)
      (mu₂.compl₂ e₂.symm.toLinearMap) p)) :
    Function.Injective (twoFamilyMultiplication mu₁ mu₂ p) := by
  intro x y hxy
  have ht := hp (show twoFamilyMultiplication (mu₁.compl₂ e₁.symm.toLinearMap)
      (mu₂.compl₂ e₂.symm.toLinearMap) p
      ((fun i => e₁ (x.1 i)),(fun i => e₂ (x.2 i))) =
      twoFamilyMultiplication (mu₁.compl₂ e₁.symm.toLinearMap)
      (mu₂.compl₂ e₂.symm.toLinearMap) p
      ((fun i => e₁ (y.1 i)),(fun i => e₂ (y.2 i))) by
    simpa only [twoFamilyMultiplication_apply,LinearMap.compl₂_apply,
      LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply] using hxy)
  apply Prod.ext
  · funext i
    exact e₁.injective (congrFun (congrArg Prod.fst ht) i)
  · funext i
    exact e₂.injective (congrFun (congrArg Prod.snd ht) i)

/-- The natural two-family count is exactly the normalized ratio condition. -/
theorem two_family_ratio_of_natural_budget {a₁ a₂ q₁ q₂ T : ℕ}
    (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hcount : (q₁+a₁)*a₁+(q₂+a₂)*a₂ ≤ T) :
    0<(T : ℝ) ∧
      ((q₁+a₁ : ℕ) : ℝ)/((T : ℝ)/a₁)+
        ((q₂+a₂ : ℕ) : ℝ)/((T : ℝ)/a₂) ≤ 1 := by
  have hT : 0<T := by nlinarith
  have hTR : (0 : ℝ)<T := by exact_mod_cast hT
  refine ⟨hTR,?_⟩
  have ha₁R : (0 : ℝ)<a₁ := by exact_mod_cast ha₁
  have ha₂R : (0 : ℝ)<a₂ := by exact_mod_cast ha₂
  have hc : (((q₁+a₁ : ℕ) : ℝ)*a₁+((q₂+a₂ : ℕ) : ℝ)*a₂)/(T : ℝ) ≤ 1 :=
    (div_le_one hTR).mpr (by exact_mod_cast hcount)
  convert hc using 1 <;> field_simp [hTR.ne',ha₁R.ne',ha₂R.ne']

end Froberg
