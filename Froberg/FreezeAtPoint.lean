import Froberg.FreezeParameters

/-! A polynomial open can be restricted to the scalar fiber through a
specified successful point, preserving all other data at that point. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K U V E : Type*} [Field K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup V] [Module K V]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem principal_open_freeze_at (F : U × V →ₗ[K] E) (u₀ : U) (v₀ : V)
    (D : MvPolynomial (Fin (finrank K E)) K)
    (hD : eval ((Module.finBasis K E).equivFun (F (u₀,v₀))) D≠0) :
    ∃ P : MvPolynomial (Fin (finrank K U)) K,
      eval ((Module.finBasis K U).equivFun u₀) P≠0 ∧
      ∀ u,eval ((Module.finBasis K U).equivFun u) P≠0 →
        eval ((Module.finBasis K E).equivFun (F (u,v₀))) D≠0 := by
  let eU := (Module.finBasis K U).equivFun
  let eE := (Module.finBasis K E).equivFun
  let L := eE.toLinearMap.comp (F.comp ((LinearMap.inl K U V).comp eU.symm.toLinearMap))
  let c := eE (F (0,v₀))
  have he (u : U) : L (eU u)+c=eE (F (u,v₀)) := by
    change eE (F (eU.symm (eU u),0))+eE (F (0,v₀))=eE (F (u,v₀))
    rw [LinearEquiv.symm_apply_apply,←map_add,←map_add]
    simp only [Prod.mk_add_mk,add_zero,zero_add]
  refine ⟨substituteAffine L c D,?_,?_⟩
  · rw [eval_substituteAffine,he]
    exact hD
  · intro u hu
    rw [eval_substituteAffine,he] at hu
    exact hu

end Froberg
