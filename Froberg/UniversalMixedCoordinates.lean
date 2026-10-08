import Froberg.UniversalMixedOpen
import Froberg.AffinePolynomialSubstitution
import Froberg.GenericDimensions
import Quartic.PolynomialBilinearCoordinates

/-! Uniform mixed position can be imposed together with an arbitrary
nonempty open in the same actual vector coordinates. -/
noncomputable section
namespace Froberg.MixedExterior
open Module MvPolynomial Quartic.PolynomialBilinearCoordinates
variable {K α : Type*} [Field K] [Infinite K] [Fintype α] [DecidableEq α]

theorem universal_mixed_coordinates_open (h : ℕ) :
    ∃ D : MvPolynomial (Fin (finrank K (α → Fin h → K))) K,
      (∃ x,eval x D≠0) ∧ ∀ x,eval x D≠0 →
        (∀ S : Finset α,S.card ≤ h → LinearIndependent K
          (fun i : S => (coordinates K (α → Fin h → K)).symm x i.val)) ∧
        UniversalMixedPosition ((coordinates K (α → Fin h → K)).symm x) := by
  classical
  obtain ⟨P,hP,hgood⟩ := universal_mixed_vectors_principal_open (K := K) (α := α) h
  let e := coordinates K (α → Fin h → K)
  let flat : (α → Fin h → K) →ₗ[K] (α × Fin h → K) :=
    { toFun := fun v p => v p.1 p.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let L : (Fin (finrank K (α → Fin h → K)) → K) →ₗ[K] (α × Fin h → K) :=
    flat.comp e.symm.toLinearMap
  have heval (x) : eval x (substituteAffine L 0 P)=eval (fun p => e.symm x p.1 p.2) P := by
    rw [eval_substituteAffine,add_zero]
    rfl
  have hex : ∃ values,eval values P≠0 := by
    by_contra hn
    push Not at hn
    apply hP
    apply MvPolynomial.funext
    intro values
    simpa only [map_zero] using hn values
  obtain ⟨values,hvalues⟩ := hex
  refine ⟨substituteAffine L 0 P,⟨e (fun i j => values (i,j)),?_⟩,?_⟩
  · rw [heval,LinearEquiv.symm_apply_apply]
    exact hvalues
  · intro x hx
    rw [heval] at hx
    exact hgood _ hx

/-- This applies in particular to the finitely many projected sparse
injectivity opens needed by the private-power rows. -/
theorem exists_universal_mixed_vectors_in_open (h : ℕ)
    (D : MvPolynomial (Fin (finrank K (α → Fin h → K))) K)
    (hD : ∃ x,eval x D≠0) :
    ∃ v : α → Fin h → K,
      eval (coordinates K _ v) D≠0 ∧
      (∀ S : Finset α,S.card ≤ h → LinearIndependent K (fun i : S => v i.val)) ∧
      UniversalMixedPosition v := by
  obtain ⟨P,hP,hgood⟩ := universal_mixed_coordinates_open (K := K) (α := α) h
  obtain ⟨x,hxD,hxP⟩ := principal_opens_intersect hD hP
  refine ⟨(coordinates K _).symm x,?_,(hgood x hxP).1,(hgood x hxP).2⟩
  simpa only [LinearEquiv.apply_symm_apply] using hxD

end Froberg.MixedExterior
