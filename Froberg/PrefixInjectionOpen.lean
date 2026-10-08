import Froberg.PrefixGrowth
import Quartic.PolynomialRankOpen

/-! The previously proved prefix injectivity witness gives an open in
intrinsic scalar-family coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic Quartic.PolynomialBilinearCoordinates
variable {K : Type*} [Field K] [Infinite K] {n d e r : ℕ}

theorem prefix_injective_principal_open (hn : 0<n) (hed : e<d)
    (hlarge : (e+d).choose e*((e+d).choose e*d.choose e)≤n)
    (hr : r*(n+e-1).choose e≤(n+(d+e)-1).choose (d+e)) :
    ∃ D : MvPolynomial (Fin (finrank K (Fin r → Forms K n d))) K,
      (∃ Q : Fin r → Forms K n d,eval (coordinates K _ Q) D≠0) ∧
      ∀ Q : Fin r → Forms K n d,eval (coordinates K _ Q) D≠0 →
        Function.Injective (prefixMultiplication Q e) := by
  obtain ⟨Q,hQ⟩ := exists_prefix_injective_of_large_variables (K := K) hn hed hlarge hr
  let c := (Module.finBasis K (Fin r → Forms K n d)).equivFun
  let A := fun x => (prefixBilinear (K := K) (n := n) (d := d) (e := e) (r := r)).flip (c.symm x)
  have hA : IsPolynomialFamily A := by
    simpa only [A,LinearMap.coe_comp,Function.comp_def,LinearMap.comp_apply,LinearEquiv.coe_coe] using
      isPolynomialFamily_linear (K := K)
        (V := (Fin r → Forms K n e) →ₗ[K] Forms K n (d+e)) ((prefixBilinear (K := K) (n := n) (d := d) (e := e) (r := r)).flip.comp
        c.symm.toLinearMap)
  obtain ⟨D,hD,hgood⟩ := injective_polynomial_principal_open A hA (c Q)
    (by simpa only [A,LinearEquiv.symm_apply_apply,prefixBilinear_flip] using hQ)
  refine ⟨D,⟨Q,hD⟩,?_⟩
  intro f hf
  simpa only [A,LinearEquiv.symm_apply_apply,prefixBilinear_flip] using hgood (c f) hf

end Froberg
