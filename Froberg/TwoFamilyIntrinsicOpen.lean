import Froberg.TwoFamilyIntrinsic
import Froberg.TwoFamilyGrowth

/-! Nonempty polynomial opens for two bilinear families with arbitrary
finite-dimensional coefficient spaces. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Quartic
variable {K P₁ P₂ V₁ V₂ W : Type*} [Field K] [Infinite K]
  [AddCommGroup P₁] [Module K P₁] [FiniteDimensional K P₁]
  [AddCommGroup P₂] [Module K P₂] [FiniteDimensional K P₂]
  [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
  [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {q₁ q₂ T : ℕ}

/-- Exact natural image growth and the finite two-family budget produce a
common principal open in the actual generator parameter space. -/
theorem two_family_generic_of_natural_growth
    (mu₁ : P₁ →ₗ[K] V₁ →ₗ[K] W) (mu₂ : P₂ →ₗ[K] V₂ →ₗ[K] W)
    (ha₁ : 0<finrank K V₁) (ha₂ : 0<finrank K V₂)
    (h₁ : ∀ L : Submodule K V₁,
      T*finrank K L ≤ finrank K V₁*finrank K (BilinearImage.image mu₁ L))
    (h₂ : ∀ L : Submodule K V₂,
      T*finrank K L ≤ finrank K V₂*finrank K (BilinearImage.image mu₂ L))
    (hcount : (q₁+finrank K V₁)*finrank K V₁+
      (q₂+finrank K V₂)*finrank K V₂ ≤ T) :
    ∃ D : MvPolynomial (Fin (finrank K ((Fin q₁ → P₁) × (Fin q₂ → P₂)))) K,
      (∃ p : (Fin q₁ → P₁) × (Fin q₂ → P₂),
        eval ((Module.finBasis K _).equivFun p) D ≠ 0) ∧
      ∀ p : (Fin q₁ → P₁) × (Fin q₂ → P₂),
        eval ((Module.finBasis K _).equivFun p) D ≠ 0 →
        Function.Injective (twoFamilyMultiplication mu₁ mu₂ p) := by
  let e₁ := (Module.finBasis K V₁).equivFun
  let e₂ := (Module.finBasis K V₂).equivFun
  let mu₁' := mu₁.compl₂ e₁.symm.toLinearMap
  let mu₂' := mu₂.compl₂ e₂.symm.toLinearMap
  have ha₁R : (0 : ℝ)<finrank K V₁ := by exact_mod_cast ha₁
  have ha₂R : (0 : ℝ)<finrank K V₂ := by exact_mod_cast ha₂
  obtain ⟨hT,hratio⟩ := two_family_ratio_of_natural_budget ha₁ ha₂ hcount
  have hg₁ (L : Submodule K (Fin (finrank K V₁) → K)) :
      ((T : ℝ)/finrank K V₁)*finrank K L ≤ finrank K (BilinearImage.image mu₁' L) := by
    have hh := h₁ (L.map e₁.symm.toLinearMap)
    rw [e₁.symm.finrank_map_eq] at hh
    dsimp only [mu₁']
    rw [bilinearImage_compl₂,div_mul_eq_mul_div]
    apply (div_le_iff₀ ha₁R).mpr
    have hc : (T : ℝ)*finrank K L ≤
        (finrank K V₁ : ℝ)*finrank K (BilinearImage.image mu₁ (L.map e₁.symm.toLinearMap)) := by
      exact_mod_cast hh
    simpa only [mul_comm] using hc
  have hg₂ (L : Submodule K (Fin (finrank K V₂) → K)) :
      ((T : ℝ)/finrank K V₂)*finrank K L ≤ finrank K (BilinearImage.image mu₂' L) := by
    have hh := h₂ (L.map e₂.symm.toLinearMap)
    rw [e₂.symm.finrank_map_eq] at hh
    dsimp only [mu₂']
    rw [bilinearImage_compl₂,div_mul_eq_mul_div]
    apply (div_le_iff₀ ha₂R).mpr
    have hc : (T : ℝ)*finrank K L ≤
        (finrank K V₂ : ℝ)*finrank K (BilinearImage.image mu₂ (L.map e₂.symm.toLinearMap)) := by
      exact_mod_cast hh
    simpa only [mul_comm] using hc
  obtain ⟨D,⟨x,hx⟩,hD⟩ := two_family_generic_of_normalized_growth
    mu₁' mu₂' (div_pos hT ha₁R) (div_pos hT ha₂R) hg₁ hg₂ hratio
  refine ⟨D,⟨(Module.finBasis K _).equivFun.symm x,?_⟩,?_⟩
  · simpa only [LinearEquiv.apply_symm_apply] using hx
  intro p hp
  have hi := hD ((Module.finBasis K _).equivFun p) hp
  rw [LinearEquiv.symm_apply_apply] at hi
  apply twoFamilyMultiplication_injective_of_coordinates e₁ e₂ mu₁ mu₂ p
  have heq : (twoFamilyBilinear mu₁' mu₂').flip p = twoFamilyMultiplication mu₁' mu₂' p := by
    apply LinearMap.ext
    intro v
    rfl
  rwa [heq] at hi

end Froberg
