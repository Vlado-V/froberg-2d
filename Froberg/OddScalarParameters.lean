module

public import Froberg.OddScalarLayers
public import Froberg.ScalarBiformParameter
public import Froberg.ParameterPullbackOpen

@[expose] public section

/-! All non-top odd-layer conditions hold on one open in the actual
linear-form and scalar-form coefficients. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type*} [Field K] [Infinite K] {h n d qO qS t : ℕ}

abbrev OddScalarParameters (K : Type*) [Field K] (h n d qO qS : ℕ) :=
  (Fin qO → Forms K h 1 ⊗[K] Forms K n (d-1)) × (Fin qS → Forms K n d)

def oddScalarBiformParameters : OddScalarParameters K h n d qO qS →ₗ[K]
    OddLayerParameters K h n d qO qS :=
  (LinearMap.fst K _ _).prod
    ((scalarBiformEquiv (K := K) (h := h) (n := n) (d := d)).toLinearMap.compLeft
      (Fin qS) |>.comp (LinearMap.snd K _ _))

theorem oddScalarBiformParameters_surjective :
    Function.Surjective (oddScalarBiformParameters (K := K) (h := h) (n := n)
      (d := d) (qO := qO) (qS := qS)) := by
  rintro ⟨F,Q⟩
  refine ⟨(F,fun i => scalarBiformEquiv.symm (Q i)),?_⟩
  apply Prod.ext
  · rfl
  · funext i
    exact (scalarBiformEquiv (K := K) (h := h) (n := n) (d := d)).apply_symm_apply (Q i)

attribute [local irreducible] OddScalarLayerProperty

theorem odd_scalar_forms_open (hopen : HasOddScalarLayersOpen K h n d qO qS t) :
    ∃ D : MvPolynomial (Fin (finrank K (OddScalarParameters K h n d qO qS))) K,
      (∃ p : OddScalarParameters K h n d qO qS,
        eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 →
        ∀ (b : ℕ) (hb : 3≤b) (hbd : b≤d),
          OddScalarLayerProperty t (by omega) hbd (oddScalarBiformParameters p) := by
  obtain ⟨D,hD,hgood⟩ := hopen
  let eU := (Module.finBasis K (OddScalarParameters K h n d qO qS)).equivFun
  let eE := (Module.finBasis K (OddLayerParameters K h n d qO qS)).equivFun
  let L := eE.toLinearMap.comp (oddScalarBiformParameters.comp eU.symm.toLinearMap)
  let P := substituteAffine L 0 D
  have heval (p : OddScalarParameters K h n d qO qS) :
      eval (eU p) P=eval (eE (oddScalarBiformParameters p)) D := by
    rw [show P=substituteAffine L 0 D from rfl,eval_substituteAffine]
    simp only [add_zero,L,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  obtain ⟨z,hz⟩ := hD
  obtain ⟨p,hp⟩ := oddScalarBiformParameters_surjective z
  refine ⟨P,⟨p,?_⟩,?_⟩
  · change eval (eU p) P≠0
    rw [heval,hp]
    exact hz
  · intro v hv b hb hbd
    apply hgood (oddScalarBiformParameters v) _ b hb hbd
    change eval (eU v) P≠0 at hv
    rw [heval] at hv
    exact hv

end Froberg
