import Froberg.FiberwisePrincipal
import Froberg.AffinePolynomialSubstitution

/-! Fiberwise nonempty opens meet arbitrary joint opens in finite-dimensional
linear parameter spaces, using their actual chosen coordinates. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K U V : Type*} [Field K] [Infinite K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem fiberwise_principal_meets_linear_joint_open
    (D : MvPolynomial (Fin (finrank K U)) K)
    (hD : ∃ u : U,eval ((Module.finBasis K U).equivFun u) D≠0)
    (Φ : U → V → Prop)
    (hΦ : ∀ u,eval ((Module.finBasis K U).equivFun u) D≠0 →
      ∃ Q : MvPolynomial (Fin (finrank K V)) K,
        (∃ v : V,eval ((Module.finBasis K V).equivFun v) Q≠0) ∧
        ∀ v,eval ((Module.finBasis K V).equivFun v) Q≠0 → Φ u v)
    (P : MvPolynomial (Fin (finrank K (U×V))) K)
    (hP : ∃ p : U×V,eval ((Module.finBasis K (U×V)).equivFun p) P≠0) :
    ∃ u v,eval ((Module.finBasis K U).equivFun u) D≠0 ∧ Φ u v ∧
      eval ((Module.finBasis K (U×V)).equivFun (u,v)) P≠0 := by
  classical
  let eU := (Module.finBasis K U).equivFun
  let eV := (Module.finBasis K V).equivFun
  let eP := (Module.finBasis K (U×V)).equivFun
  let F : ((Fin (finrank K U) ⊕ Fin (finrank K V)) → K) →ₗ[K]
      (Fin (finrank K (U×V)) → K) :=
    eP.toLinearMap.comp ((eU.symm.toLinearMap.comp (LinearMap.funLeft K K Sum.inl)).prod
      (eV.symm.toLinearMap.comp (LinearMap.funLeft K K Sum.inr)))
  have heval (x : Fin (finrank K U) → K) (y : Fin (finrank K V) → K) :
      eval (Sum.elim x y) (substituteAffine F 0 P)=eval (eP (eU.symm x,eV.symm y)) P := by
    rw [eval_substituteAffine,add_zero]
    rfl
  have hP' : ∃ z,eval z (substituteAffine F 0 P)≠0 := by
    obtain ⟨⟨u,v⟩,hp⟩ := hP
    refine ⟨Sum.elim (eU u) (eV v),?_⟩
    simpa only [heval,LinearEquiv.symm_apply_apply] using hp
  have hD' : ∃ x,eval x D≠0 := by
    obtain ⟨u,hu⟩ := hD
    exact ⟨eU u,hu⟩
  have hfiber : ∀ x,eval x D≠0 → ∃ Q : MvPolynomial (Fin (finrank K V)) K,
      (∃ y,eval y Q≠0) ∧ ∀ y,eval y Q≠0 → Φ (eU.symm x) (eV.symm y) := by
    intro x hx
    obtain ⟨Q,⟨v,hv⟩,hQ⟩ := hΦ (eU.symm x) (by simpa only [eU,eV,LinearEquiv.apply_symm_apply] using hx)
    refine ⟨Q,⟨eV v,hv⟩,?_⟩
    intro y hy
    exact hQ _ (by simpa only [eU,eV,LinearEquiv.apply_symm_apply] using hy)
  obtain ⟨x,y,hx,hxy,hp⟩ := fiberwise_principal_meets_joint_open D hD' _ hfiber _ hP'
  exact ⟨eU.symm x,eV.symm y,by simpa only [eU,eV,LinearEquiv.apply_symm_apply] using hx,
    hxy,by simpa only [heval] using hp⟩

end Froberg
