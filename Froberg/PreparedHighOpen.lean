import Froberg.PreparedPositiveLeadingOpen
import Froberg.RestoredOuterIndependence

/-! Independent positive leading parts form a nonempty open on the full
restored parameter space, independently of the scalar and pure entries. -/
noncomputable section
set_option maxHeartbeats 250000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def highPartLinear (j : J) (i : Fin (counts j.val)) :
    Space m d q J counts O →ₗ[K] biformImage (O j.val) (Forms K m (d-j.val)) where
  toFun p := p.2 j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem positive_high_principal_open
    (hO : ∀ j∈J,O j≤Forms K h j)
    (hw : ∀ j : J,∃ p : Space m d q J counts O,LinearIndependent K (p.2 j)) :
    letI : Module.Finite K (Space m d q J counts O) := finite_space hO
    ∃ D : MvPolynomial (Fin (finrank K (Space m d q J counts O))) K,
      (∃ p : Space m d q J counts O,eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p : Space m d q J counts O,eval ((Module.finBasis K _).equivFun p) D≠0 →
        ∀ j,LinearIndependent K (p.2 j) := by
  classical
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  let coord := (Module.finBasis K (Space m d q J counts O)).equivFun
  have hrow (j : J) : ∃ D : MvPolynomial (Fin (finrank K (Space m d q J counts O))) K,
      (∃ p : Space m d q J counts O,eval (coord p) D≠0) ∧
      ∀ p : Space m d q J counts O,eval (coord p) D≠0 → LinearIndependent K (p.2 j) := by
    obtain ⟨p,hp⟩ := hw j
    obtain ⟨D,hD,hgood⟩ := independent_principal_open
      (fun i => (highPartLinear j i).comp coord.symm.toLinearMap) (coord p)
      (by simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,
        highPartLinear,LinearMap.coe_mk,AddHom.coe_mk] using hp)
    refine ⟨D,⟨p,hD⟩,?_⟩
    intro p hp
    simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,
      highPartLinear,LinearMap.coe_mk,AddHom.coe_mk] using hgood (coord p) hp
  choose D hD hgood using hrow
  obtain ⟨p,hp⟩ := finite_basis_principal_intersection D hD
  refine ⟨∏ j,D j,⟨p,?_⟩,?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hp j)
  · intro p hp j
    rw [map_prod] at hp
    exact hgood j p (Finset.prod_ne_zero_iff.mp hp j (Finset.mem_univ j))

def restoredPreparedProjection : RestoredOuterSpace m d q f J counts O →ₗ[K]
    Space m d q J counts O :=
  (LinearMap.fst K _ _).comp (LinearMap.fst K _ _)

theorem restored_positive_high_principal_open
    (hO : ∀ j∈J,O j≤Forms K h j)
    (hw : ∀ j : J,∃ p : Space m d q J counts O,LinearIndependent K (p.2 j)) :
    letI : Module.Finite K (Space m d q J counts O) := finite_space hO
    ∃ D : MvPolynomial (Fin (finrank K (RestoredOuterSpace m d q f J counts O))) K,
      (∃ p : RestoredOuterSpace m d q f J counts O,eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p : RestoredOuterSpace m d q f J counts O,eval ((Module.finBasis K _).equivFun p) D≠0 →
        ∀ j,LinearIndependent K (p.1.1.2 j) := by
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  obtain ⟨D,hD,hgood⟩ := positive_high_principal_open hO hw
  exact principal_open_linear_pullback restoredPreparedProjection (fun p => ⟨((p,0),0),rfl⟩)
    D hD _ hgood

end Froberg.PreparedParameters
