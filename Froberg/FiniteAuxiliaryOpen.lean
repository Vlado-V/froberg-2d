import Froberg.FreezeParameters
import Quartic.PolynomialRankOpen

/-! Intersect all chart opens before fixing the auxiliary slice parameters,
so the same number of cuts works simultaneously on every chart. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K U V C : Type*} [Field K] [Infinite K] [Fintype C]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem principal_open_fixed_auxiliary_finite (Good : C → U × V → Prop)
    (h : ∀ c,∃ D : MvPolynomial (Fin (finrank K (U × V))) K,
      (∃ p : U × V,eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 → Good c p) :
    ∃ v : V,∃ P : MvPolynomial (Fin (finrank K U)) K,
      (∃ u : U,eval ((Module.finBasis K _).equivFun u) P≠0) ∧
      ∀ u,eval ((Module.finBasis K _).equivFun u) P≠0 → ∀ c,Good c (u,v) := by
  classical
  choose D hD hgood using h
  have hnz (c : C) : D c≠0 := by
    obtain ⟨p,hp⟩ := hD c
    intro hz
    exact hp (by rw [hz,map_zero])
  obtain ⟨x,hx⟩ := Quartic.nonempty_principal_intersection D hnz
  have hprod : ∃ p : U × V,eval ((Module.finBasis K _).equivFun p) (∏ c,D c)≠0 := by
    refine ⟨(Module.finBasis K _).equivFun.symm x,?_⟩
    simp only [LinearEquiv.apply_symm_apply,map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun c _ => hx c)
  have hg : ∀ p : U × V,eval ((Module.finBasis K _).equivFun p) (∏ c,D c)≠0 → ∀ c,Good c p := by
    intro p hp c
    apply hgood c p
    rw [map_prod] at hp
    exact Finset.prod_ne_zero_iff.mp hp c (Finset.mem_univ c)
  exact principal_open_freeze_right (∏ c,D c) hprod (fun p => ∀ c,Good c p) hg

end Froberg
