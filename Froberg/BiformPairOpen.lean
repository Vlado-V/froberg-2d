module

public import Froberg.BiformFullRow

@[expose] public section

/-! Rank certificates in the full two-layer biform parameter space. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct Quartic
variable {K P E F T : Type*} [Field K]
  [AddCommGroup E] [Module K E] [Module.Finite K E]
  [AddCommGroup F] [Module K F] [Module.Finite K F]
  [AddCommGroup T] [Module K T] [Module.Finite K T]

theorem polynomial_coprod (A : (P → K) → E →ₗ[K] T) (B : (P → K) → F →ₗ[K] T)
    (hA : IsPolynomialFamily A) (hB : IsPolynomialFamily B) :
    IsPolynomialFamily (fun a => (A a).coprod (B a)) := by
  apply isPolynomialFamily_linearMap
  intro z
  simpa only [LinearMap.coprod_apply,LinearMap.applyₗ_apply_apply] using
    (hA.linear_comp (LinearMap.applyₗ (R := K) (M₂ := T) z.1)).add
      (hB.linear_comp (LinearMap.applyₗ (R := K) (M₂ := T) z.2))

theorem coprod_surjective_principal_open
    (A : (P → K) → E →ₗ[K] T) (B : (P → K) → F →ₗ[K] T)
    (hA : IsPolynomialFamily A) (hB : IsPolynomialFamily B) (a₀ : P → K)
    (ha₀ : Function.Surjective ((A a₀).coprod (B a₀))) :
    ∃ D : MvPolynomial P K, eval a₀ D ≠ 0 ∧ ∀ a, eval a D ≠ 0 →
      Function.Surjective ((A a).coprod (B a)) := by
  obtain ⟨D,hD,hRank⟩ := rank_polynomial_principal_open
    (fun a => (A a).coprod (B a)) (polynomial_coprod A B hA hB) a₀
  refine ⟨D,hD,fun a ha => ?_⟩
  have hr := hRank a ha
  rw [LinearMap.range_eq_top.mpr ha₀,finrank_top] at hr
  apply LinearMap.range_eq_top.mp
  exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) hr)

variable {r q h m s e y : ℕ}
attribute [local instance] tensorGroup

theorem row_two_full_principal_open
    (g₁ : (P → K) → Fin r → Forms K h 1 ⊗[K] Forms K m s)
    (g₂ : (P → K) → Fin q → Forms K h 2 ⊗[K] Forms K m e)
    (hg₁ : IsPolynomialFamily g₁) (hg₂ : IsPolynomialFamily g₂) (he : e+y=s+s)
    (a₀ : P → K)
    (ha₀ : Function.Surjective ((biformTensorFamilyMap (x := 1) (y := s) (g₁ a₀)).coprod
      (biformTensorFamilyToDegree (x := 0) he (g₂ a₀)))) :
    ∃ D : MvPolynomial P K, eval a₀ D ≠ 0 ∧ ∀ a, eval a D ≠ 0 →
      Function.Surjective ((biformTensorFamilyMap (x := 1) (y := s) (g₁ a)).coprod
        (biformTensorFamilyToDegree (x := 0) he (g₂ a))) := by
  exact coprod_surjective_principal_open _ _
    (hg₁.linear_comp (biformTensorFamilyMap (x := 1) (y := s)))
    (hg₂.linear_comp (biformTensorFamilyToDegree (x := 0) he)) a₀ ha₀

end Froberg
