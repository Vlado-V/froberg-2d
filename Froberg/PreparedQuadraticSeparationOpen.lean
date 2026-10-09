module

public import Froberg.QuadraticSeparationRow
public import Froberg.FullPreparedProjections

@[expose] public section

/-! The quadratic coefficient row is polynomial on the full prepared
parameter space. Its scalar, private, and outer inputs are independent
linear coordinates, so every supplied row witness lifts to that space. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.FullPreparedParameters
open Froberg Module MvPolynomial PreparedParameters PreparedTarget Quartic
variable {K : Type} [Field K] [Infinite K]
variable {h m d q r f u t c : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

abbrev PreparedQuadraticParameters (K : Type) [Field K] (h m d r f u : ℕ) :=
  (Fin r → Forms K m d) × (OuterSpace K (Fin h) m d u × OuterSpace K (Fin h) m d f)

def preparedQuadraticProjection (idx : Fin r ≃ PreparedParameters.Label q J counts) :
    FixedPureZeroScalarSpace m d q f u J counts O →ₗ[K]
      PreparedQuadraticParameters K h m d r f u where
  toFun p := (fun i => p.2.1.1 (idx i),p.1,p.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem preparedQuadraticProjection_surjective (idx : Fin r ≃ PreparedParameters.Label q J counts) :
    Function.Surjective (preparedQuadraticProjection (K := K) (h := h) (m := m) (d := d)
      (f := f) (u := u) (O := O) idx) := by
  rintro ⟨Q,P,F⟩
  refine ⟨(P,((fun i => Q (idx.symm i),0),F)),?_⟩
  apply Prod.ext
  · funext i
    exact congrArg Q (idx.symm_apply_apply i)
  · rfl

def PreparedQuadraticRowSeparated
    (idx : Fin r ≃ PreparedParameters.Label q J counts)
    (T : MvPolynomial (Fin h ⊕ Fin m) K →ₗ[K] (Fin c → Poly K m))
    (p : FixedPureZeroScalarSpace m d q f u J counts O) : Prop :=
  ∀ x z,quadraticNuisanceRow (t := t) (FullBiform K (Fin h) m 1 (d-1)).subtype T
      (fun i => p.2.1.1 (idx i)) p.1 x+
    detectedSymmetricProductRow (FullBiform K (Fin h) m 1 (d-1)).subtype T p.2.2 z=0 → z=0

theorem prepared_quadratic_separation_principal_open
    (hO : ∀ j∈J,O j≤Forms K h j)
    (idx : Fin r ≃ PreparedParameters.Label q J counts)
    (T : MvPolynomial (Fin h ⊕ Fin m) K →ₗ[K] (Fin c → Poly K m))
    (Q₀ : Fin r → Forms K m d) (P₀ : OuterSpace K (Fin h) m d u)
    (F₀ : OuterSpace K (Fin h) m d f)
    (hexact : (quadraticNuisanceRow (t := t) (FullBiform K (Fin h) m 1 (d-1)).subtype T Q₀ P₀).ker=
      (quadraticNuisanceBoundary P₀).range)
    (hsep : ∀ x z,quadraticNuisanceRow (t := t) (FullBiform K (Fin h) m 1 (d-1)).subtype T Q₀ P₀ x+
      detectedSymmetricProductRow (FullBiform K (Fin h) m 1 (d-1)).subtype T F₀ z=0 → z=0) :
    letI : Module.Finite K (FixedPureZeroScalarSpace m d q f u J counts O) :=
      finite_fixedPureZeroScalarSpace hO
    ∃ D : MvPolynomial (Fin (finrank K (FixedPureZeroScalarSpace m d q f u J counts O))) K,
      (∃ p : FixedPureZeroScalarSpace m d q f u J counts O,
        eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p : FixedPureZeroScalarSpace m d q f u J counts O,
        eval ((Module.finBasis K _).equivFun p) D≠0 →
          PreparedQuadraticRowSeparated (t := t) idx T p := by
  classical
  letI : Module.Finite K (FixedPureZeroScalarSpace m d q f u J counts O) :=
    finite_fixedPureZeroScalarSpace hO
  let b := Module.finBasis K (FixedPureZeroScalarSpace m d q f u J counts O)
  let L := (preparedQuadraticProjection (K := K) (h := h) (m := m) (d := d)
    (f := f) (u := u) (O := O) idx).comp b.equivFun.symm.toLinearMap
  let Q := fun a => (L a).1
  let P := fun a => (L a).2.1
  let F := fun a => (L a).2.2
  let C := fun a => detectedSymmetricProductRow (FullBiform K (Fin h) m 1 (d-1)).subtype T (F a)
  have hQ : IsPolynomialFamily Q :=
    isPolynomialFamily_linear ((LinearMap.fst K _ _).comp L)
  have hP : IsPolynomialFamily P :=
    isPolynomialFamily_linear ((LinearMap.fst K _ _).comp ((LinearMap.snd K _ _).comp L))
  have hF : IsPolynomialFamily F :=
    isPolynomialFamily_linear ((LinearMap.snd K _ _).comp ((LinearMap.snd K _ _).comp L))
  have hC : IsPolynomialFamily C :=
    detectedSymmetricProductRow_polynomial _ _ F hF
  obtain ⟨p₀,hp₀⟩ := preparedQuadraticProjection_surjective (K := K) (h := h) (m := m) (d := d)
    (f := f) (u := u) (O := O) idx (Q₀,P₀,F₀)
  have hL (p : FixedPureZeroScalarSpace m d q f u J counts O) :
      L (b.equivFun p)=preparedQuadraticProjection idx p := by
    simp only [L,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  have hzero : L (b.equivFun p₀)=(Q₀,P₀,F₀) := (hL p₀).trans hp₀
  obtain ⟨D,hD,hgood⟩ := quadratic_nuisance_separation_open
    (FullBiform K (Fin h) m 1 (d-1)).subtype T Q P C hQ hP hC (b.equivFun p₀)
    (by simpa only [Q,P,hzero] using hexact)
    (by simpa only [Q,P,C,F,hzero] using hsep)
  refine ⟨D,⟨p₀,hD⟩,?_⟩
  intro p hp
  have hh := hgood (b.equivFun p) hp
  simpa only [Q,P,C,F,hL,PreparedQuadraticRowSeparated,preparedQuadraticProjection,
    LinearMap.coe_mk,AddHom.coe_mk] using hh

end Froberg.FullPreparedParameters
