module

public import Froberg.AffinePolynomialSubstitution

@[expose] public section

/-! A certified principal open pulls back through a surjective linear
parameter map, retaining a nonzero evaluation at an actual preimage. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K U E : Type*} [Field K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem principal_open_linear_pullback (F : U →ₗ[K] E) (hF : Function.Surjective F)
    (D : MvPolynomial (Fin (finrank K E)) K)
    (hD : ∃ e : E,eval ((Module.finBasis K E).equivFun e) D≠0)
    (Good : E → Prop)
    (hGood : ∀ e,eval ((Module.finBasis K E).equivFun e) D≠0 → Good e) :
    ∃ P : MvPolynomial (Fin (finrank K U)) K,
      (∃ u : U,eval ((Module.finBasis K U).equivFun u) P≠0) ∧
      ∀ u,eval ((Module.finBasis K U).equivFun u) P≠0 → Good (F u) := by
  let eU := (Module.finBasis K U).equivFun
  let eE := (Module.finBasis K E).equivFun
  let L := eE.toLinearMap.comp (F.comp eU.symm.toLinearMap)
  let P := substituteAffine L 0 D
  have heval (u : U) : eval (eU u) P=eval (eE (F u)) D := by
    rw [show P=substituteAffine L 0 D from rfl,eval_substituteAffine]
    simp only [add_zero,L,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  obtain ⟨e,he⟩ := hD
  obtain ⟨u,hu⟩ := hF e
  refine ⟨P,⟨u,?_⟩,?_⟩
  · change eval (eU u) P≠0
    rw [heval,hu]
    exact he
  · intro v hv
    apply hGood
    change eval (eU v) P≠0 at hv
    rw [heval] at hv
    exact hv

end Froberg
