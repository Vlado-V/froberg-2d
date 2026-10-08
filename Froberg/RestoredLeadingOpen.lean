import Froberg.PreparedPositiveLeadingOpen
import Froberg.RestoredQuadraticParameters

/-! Actual witnesses for each positive row give one nonempty principal
open where all restored leading families are independent. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def restoredHighLinear (j : J) (i : Fin (counts j.val)) :
    RestoredOuterSpace m d q f J counts O →ₗ[K]
      biformImage (O j.val) (Forms K m (d-j.val)) where
  toFun p := p.1.1.2 j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restored_leading_principal_open
    (hO : ∀ j∈J,O j≤Forms K h j)
    (hw : ∀ j : J,∃ p : Space m d q J counts O,LinearIndependent K (p.2 j)) :
    letI : Module.Finite K (Space m d q J counts O) := finite_space hO
    ∃ D : MvPolynomial (Fin (finrank K (RestoredOuterSpace m d q f J counts O))) K,
      (∃ p : RestoredOuterSpace m d q f J counts O,
        eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p : RestoredOuterSpace m d q f J counts O,
        eval ((Module.finBasis K _).equivFun p) D≠0 →
        ∀ j,LinearIndependent K (p.1.1.2 j) := by
  classical
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  let coord := (Module.finBasis K (RestoredOuterSpace m d q f J counts O)).equivFun
  have hrow (j : J) :
      ∃ D : MvPolynomial (Fin (finrank K (RestoredOuterSpace m d q f J counts O))) K,
        (∃ p : RestoredOuterSpace m d q f J counts O,eval (coord p) D≠0) ∧
        ∀ p : RestoredOuterSpace m d q f J counts O,
          eval (coord p) D≠0 → LinearIndependent K (p.1.1.2 j) := by
    obtain ⟨p,hp⟩ := hw j
    obtain ⟨D,hD,hgood⟩ := independent_principal_open
      (fun i => (restoredHighLinear j i).comp coord.symm.toLinearMap) (coord ((p,0),0))
      (by simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,
        restoredHighLinear,LinearMap.coe_mk,AddHom.coe_mk] using hp)
    refine ⟨D,⟨((p,0),0),hD⟩,?_⟩
    intro p hp
    simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,
      restoredHighLinear,LinearMap.coe_mk,AddHom.coe_mk] using hgood (coord p) hp
  choose D hD hgood using hrow
  obtain ⟨p,hp⟩ := finite_basis_principal_intersection D hD
  refine ⟨∏ j,D j,⟨p,?_⟩,?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hp j)
  · intro p hp j
    rw [map_prod] at hp
    exact hgood j p (Finset.prod_ne_zero_iff.mp hp j (Finset.mem_univ j))

end Froberg.PreparedParameters
