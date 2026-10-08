import Froberg.VectorParameters
import Froberg.AffinePolynomialSubstitution

/-! The strict vector model opens use monomial coefficients. This exact
coordinate change supplies principal opens in the canonical finite basis
used by the prepared-family selection theorems. -/
noncomputable section
namespace Froberg.VectorParameters
open Module MvPolynomial Quartic VectorMultiplicationCoordinates
variable {K : Type*} [Field K] {h n s c : ℕ}

def generatorsEquiv : (Index h n s c → K) ≃ₗ[K] (Fin c → Rows K h n s) where
  toFun := generators
  invFun := coordinates
  left_inv := coordinates_generators
  right_inv := generators_coordinates
  map_add' p q := by
    funext i
    exact rowFiniteEquiv.symm.map_add _ _
  map_smul' a p := by
    funext i
    exact rowFiniteEquiv.symm.map_smul a _

theorem principal_open_in_finite_coordinates
    (D : MvPolynomial (Index h n s c) K) (hD : ∃ p,eval p D≠0)
    (Good : (Fin c → Rows K h n s) → Prop)
    (hgood : ∀ p,eval p D≠0 → Good (generators p)) :
    ∃ P : MvPolynomial (Fin (finrank K (Fin c → Rows K h n s))) K,
      (∃ g : Fin c → Rows K h n s,eval ((Module.finBasis K _).equivFun g) P≠0) ∧
      ∀ g : Fin c → Rows K h n s,eval ((Module.finBasis K _).equivFun g) P≠0 → Good g := by
  let e := (Module.finBasis K (Fin c → Rows K h n s)).equivFun
  let L := (generatorsEquiv (K := K) (h := h) (n := n) (s := s) (c := c)).symm.toLinearMap.comp
    e.symm.toLinearMap
  let P := substituteAffine L 0 D
  have heval (g : Fin c → Rows K h n s) : eval (e g) P=eval (coordinates g) D := by
    rw [show P=substituteAffine L 0 D from rfl,eval_substituteAffine,add_zero]
    change eval (coordinates (e.symm (e g))) D=eval (coordinates g) D
    rw [LinearEquiv.symm_apply_apply]
  obtain ⟨p,hp⟩ := hD
  refine ⟨P,⟨generators p,?_⟩,?_⟩
  · change eval (e (generators p)) P≠0
    rwa [heval,coordinates_generators]
  · intro g hg
    rw [show (Module.finBasis K _).equivFun g=e g from rfl,heval] at hg
    simpa only [generators_coordinates] using hgood (coordinates g) hg

end Froberg.VectorParameters
