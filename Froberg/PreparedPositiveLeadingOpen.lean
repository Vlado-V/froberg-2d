import Froberg.PreparedPositiveIndependence
import Froberg.FiniteBasisPrincipalIntersection
import Froberg.PreparedIndependenceOpen

/-! Independent positive leading parts can be imposed simultaneously on
the full prepared parameter space using the actual row witnesses. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def fullHighLinear (j : J) (i : Fin (counts j.val)) :
    FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O →ₗ[K]
      biformImage (O j.val) (Forms K m (d-j.val)) where
  toFun p := p.2.1.2 j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def fullPrivateLinear (i : Fin u) :
    FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O →ₗ[K]
      biformImage (Forms K h 1) (Forms K m (d-1)) where
  toFun p := p.1 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem positive_leading_principal_open
    (hO : ∀ j∈J,O j≤Forms K h j)
    (hw : ∀ j : J,∃ p : Space m d q J counts O,LinearIndependent K (p.2 j))
    (P₀ : PreparedTarget.OuterSpace K (Fin h) m d u) (hP₀ : LinearIndependent K P₀) :
    letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
      FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
    ∃ D : MvPolynomial (Fin (finrank K
      (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O))) K,
      (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
        eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
        eval ((Module.finBasis K _).equivFun p) D≠0 →
        (∀ j,LinearIndependent K (p.2.1.2 j)) ∧ LinearIndependent K p.1 := by
  classical
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  let coord := (Module.finBasis K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O)).equivFun
  have hrow (j : J) : ∃ D : MvPolynomial (Fin (finrank K
      (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O))) K,
      (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,eval (coord p) D≠0) ∧
      ∀ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
        eval (coord p) D≠0 → LinearIndependent K (p.2.1.2 j) := by
    obtain ⟨p,hp⟩ := hw j
    obtain ⟨D,hD,hgood⟩ := independent_principal_open
      (fun i => (fullHighLinear j i).comp coord.symm.toLinearMap) (coord (0,(p,0)))
      (by simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,
        fullHighLinear,LinearMap.coe_mk,AddHom.coe_mk] using hp)
    refine ⟨D,⟨(0,(p,0)),hD⟩,?_⟩
    intro p hp
    simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,
      fullHighLinear,LinearMap.coe_mk,AddHom.coe_mk] using hgood (coord p) hp
  choose D hD hgood using hrow
  obtain ⟨P,hP,hPgood⟩ := independent_principal_open
    (fun i => (fullPrivateLinear i).comp coord.symm.toLinearMap) (coord (P₀,(0,0)))
    (by simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,
      fullPrivateLinear,LinearMap.coe_mk,AddHom.coe_mk] using hP₀)
  let family : Option J → MvPolynomial (Fin (finrank K
      (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O))) K := Option.elim' P D
  have hex (j : Option J) : ∃ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
      eval (coord p) (family j)≠0 := by
    cases j with
    | none => exact ⟨(P₀,(0,0)),hP⟩
    | some j => exact hD j
  obtain ⟨p,hp⟩ := finite_basis_principal_intersection family hex
  refine ⟨∏ j,family j,⟨p,?_⟩,?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hp j)
  · intro p hp
    rw [map_prod] at hp
    have hall (j : Option J) := Finset.prod_ne_zero_iff.mp hp j (Finset.mem_univ j)
    refine ⟨fun j => hgood j p (hall (some j)),?_⟩
    simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,
      fullPrivateLinear,LinearMap.coe_mk,AddHom.coe_mk] using hPgood (coord p) (hall none)

end Froberg.PreparedParameters
