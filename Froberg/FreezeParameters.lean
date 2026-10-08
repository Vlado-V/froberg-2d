import Froberg.AffinePolynomialSubstitution

/-! A nonempty principal parameter open remains nonempty after fixing a
suitable value of the auxiliary parameters. The parameterization may be any
surjective linear map onto the original coefficient space. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K U V E : Type*} [Field K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup V] [Module K V]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem principal_open_freeze_parameters (F : U × V →ₗ[K] E)
    (hF : Function.Surjective F)
    (D : MvPolynomial (Fin (finrank K E)) K)
    (hD : ∃ e : E,eval ((Module.finBasis K E).equivFun e) D≠0)
    (Good : E → Prop)
    (hGood : ∀ e,eval ((Module.finBasis K E).equivFun e) D≠0 → Good e) :
    ∃ v : V,∃ P : MvPolynomial (Fin (finrank K U)) K,
      (∃ u : U,eval ((Module.finBasis K U).equivFun u) P≠0) ∧
      ∀ u,eval ((Module.finBasis K U).equivFun u) P≠0 → Good (F (u,v)) := by
  classical
  obtain ⟨e,he⟩ := hD
  obtain ⟨⟨u,v⟩,huv⟩ := hF e
  let eU := (Module.finBasis K U).equivFun
  let eE := (Module.finBasis K E).equivFun
  let L := eE.toLinearMap.comp (F.comp ((LinearMap.inl K U V).comp eU.symm.toLinearMap))
  let c := eE (F (0,v))
  have hLc (x : Fin (finrank K U) → K) : L x+c=eE (F (eU.symm x,v)) := by
    change eE (F (eU.symm x,0))+eE (F (0,v))=eE (F (eU.symm x,v))
    rw [←map_add,←map_add]
    simp only [Prod.mk_add_mk,add_zero,zero_add]
  refine ⟨v,substituteAffine L c D,⟨u,?_⟩,?_⟩
  · rw [eval_substituteAffine,hLc]
    simpa only [eU,LinearEquiv.symm_apply_apply,huv,eE] using he
  · intro x hx
    rw [eval_substituteAffine,hLc] at hx
    apply hGood
    simpa only [eU,LinearEquiv.symm_apply_apply,eE] using hx

/-- Fixing the auxiliary factor requires neither an infinite field nor a
new genericity assumption: the original nonzero evaluation is retained. -/
theorem principal_open_freeze_right
    (D : MvPolynomial (Fin (finrank K (U × V))) K)
    [FiniteDimensional K V]
    (hD : ∃ e : U × V,eval ((Module.finBasis K (U × V)).equivFun e) D≠0)
    (Good : U × V → Prop)
    (hGood : ∀ e,eval ((Module.finBasis K (U × V)).equivFun e) D≠0 → Good e) :
    ∃ v : V,∃ P : MvPolynomial (Fin (finrank K U)) K,
      (∃ u : U,eval ((Module.finBasis K U).equivFun u) P≠0) ∧
      ∀ u,eval ((Module.finBasis K U).equivFun u) P≠0 → Good (u,v) :=
  principal_open_freeze_parameters (LinearMap.id : U × V →ₗ[K] U × V)
    Function.surjective_id D hD Good hGood

end Froberg
