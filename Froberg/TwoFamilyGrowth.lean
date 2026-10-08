import Froberg.TwoFamilyGeneric
import Froberg.TwoFamilyBudget
import Froberg.BilinearScalarFamily

/-! Two actual bilinear generator families are simultaneously independent
when their normalized dimension ratios, including coefficient overhead, fit. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic Quartic.ProjectiveKernelIncidence
variable {K P₁ P₂ W : Type*} [Field K] [Infinite K]
  [AddCommGroup P₁] [Module K P₁] [FiniteDimensional K P₁]
  [AddCommGroup P₂] [Module K P₂] [FiniteDimensional K P₂]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {a₁ a₂ q₁ q₂ : ℕ}

def twoFamilyBilinear
    (mu₁ : P₁ →ₗ[K] (Fin a₁ → K) →ₗ[K] W)
    (mu₂ : P₂ →ₗ[K] (Fin a₂ → K) →ₗ[K] W) :
    ((Fin q₁ → Fin a₁ → K) × (Fin q₂ → Fin a₂ → K)) →ₗ[K]
      ((Fin q₁ → P₁) × (Fin q₂ → P₂)) →ₗ[K] W where
  toFun x := (BilinearScalarFamily.tupleBilinear mu₁ x.1).comp (LinearMap.fst K _ _) +
    (BilinearScalarFamily.tupleBilinear mu₂ x.2).comp (LinearMap.snd K _ _)
  map_add' x y := by
    apply LinearMap.ext
    intro p
    simp only [Prod.fst_add,Prod.snd_add,map_add,LinearMap.add_comp,
      LinearMap.add_apply,LinearMap.comp_apply]
    abel
  map_smul' c x := by
    apply LinearMap.ext
    intro p
    simp only [Prod.smul_fst,Prod.smul_snd,map_smul,LinearMap.smul_comp,
      LinearMap.comp_apply,
      LinearMap.smul_apply,LinearMap.add_apply,smul_add,RingHom.id_apply]

@[simp] theorem twoFamilyBilinear_apply
    (mu₁ : P₁ →ₗ[K] (Fin a₁ → K) →ₗ[K] W)
    (mu₂ : P₂ →ₗ[K] (Fin a₂ → K) →ₗ[K] W)
    (x : (Fin q₁ → Fin a₁ → K) × (Fin q₂ → Fin a₂ → K))
    (p : (Fin q₁ → P₁) × (Fin q₂ → P₂)) :
    twoFamilyBilinear mu₁ mu₂ x p =
      BilinearImage.tupleMap mu₁ x.1 p.1+BilinearImage.tupleMap mu₂ x.2 p.2 := rfl

theorem twoFamilyBilinear_left_range
    (mu₁ : P₁ →ₗ[K] (Fin a₁ → K) →ₗ[K] W)
    (mu₂ : P₂ →ₗ[K] (Fin a₂ → K) →ₗ[K] W)
    (x : (Fin q₁ → Fin a₁ → K) × (Fin q₂ → Fin a₂ → K)) :
    BilinearImage.image mu₁ (tupleSpan x.1) ≤ (twoFamilyBilinear mu₁ mu₂ x).range := by
  change BilinearImage.image _ (Submodule.span K (Set.range _)) ≤ _
  rw [← BilinearImage.range_tupleMap]
  rintro y ⟨p,rfl⟩
  exact ⟨(p,0),by simp⟩

theorem twoFamilyBilinear_right_range
    (mu₁ : P₁ →ₗ[K] (Fin a₁ → K) →ₗ[K] W)
    (mu₂ : P₂ →ₗ[K] (Fin a₂ → K) →ₗ[K] W)
    (x : (Fin q₁ → Fin a₁ → K) × (Fin q₂ → Fin a₂ → K)) :
    BilinearImage.image mu₂ (tupleSpan x.2) ≤ (twoFamilyBilinear mu₁ mu₂ x).range := by
  change BilinearImage.image _ (Submodule.span K (Set.range _)) ≤ _
  rw [← BilinearImage.range_tupleMap]
  rintro y ⟨p,rfl⟩
  exact ⟨(0,p),by simp⟩

/-- A literal common open of the two generator parameter spaces. -/
theorem two_family_generic_of_normalized_growth
    (mu₁ : P₁ →ₗ[K] (Fin a₁ → K) →ₗ[K] W)
    (mu₂ : P₂ →ₗ[K] (Fin a₂ → K) →ₗ[K] W)
    {R₁ R₂ : ℝ} (hR₁ : 0<R₁) (hR₂ : 0<R₂)
    (h₁ : ∀ L : Submodule K (Fin a₁ → K), R₁*finrank K L ≤
      finrank K (BilinearImage.image mu₁ L))
    (h₂ : ∀ L : Submodule K (Fin a₂ → K), R₂*finrank K L ≤
      finrank K (BilinearImage.image mu₂ L))
    (hratio : ((q₁+a₁ : ℕ) : ℝ)/R₁+((q₂+a₂ : ℕ) : ℝ)/R₂≤1) :
    ∃ D : MvPolynomial (Fin (finrank K ((Fin q₁ → P₁) × (Fin q₂ → P₂)))) K,
      (∃ p, eval p D ≠ 0) ∧ ∀ p, eval p D ≠ 0 →
        Function.Injective ((twoFamilyBilinear mu₁ mu₂).flip
          ((Module.finBasis K ((Fin q₁ → P₁) × (Fin q₂ → P₂))).equivFun.symm p)) := by
  apply two_family_generic_injective
  intro x _
  apply two_family_incidence_budget hR₁ hR₂ _ _ hratio
  · exact (h₁ (tupleSpan x.1)).trans (by
      exact_mod_cast Submodule.finrank_mono (twoFamilyBilinear_left_range mu₁ mu₂ x))
  · exact (h₂ (tupleSpan x.2)).trans (by
      exact_mod_cast Submodule.finrank_mono (twoFamilyBilinear_right_range mu₁ mu₂ x))

end Froberg
