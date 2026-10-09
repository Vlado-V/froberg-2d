module

public import Quartic.SmallCovectorMotion
public import Quartic.AugmentedGenericOmega

@[expose] public section

noncomputable section
namespace Quartic.SmallCovectorMotionOmega
open Module MvPolynomial UniformEndpoint ProfileCertificate
open PolynomialBilinearCoordinates
variable {K : Type*} [Field K] (ω : K)

theorem augmented_motion_open {m c q N : ℕ}
    (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2)
    (e : (Fin 4 → Forms K m 2) ≃ₗ[K] (Fin N → K))
    (r₀ : Fin 4 → Forms K m 2) (hh : LinearIndependent K h)
    (hr₀ : Function.Injective
      (AugmentedGenericOmega.quotientAugmented ω (AugmentedGeneric.productMap g) h r₀)) :
    ∃ D : MvPolynomial (Fin N) K,eval (e r₀) D ≠ 0 ∧ ∀ x,eval x D ≠ 0 →
      Function.Injective (AugmentedGenericOmega.quotientAugmented ω
        (AugmentedGeneric.productMap g) h (e.symm x)) := by
  classical
  have hpoly := AugmentedGenericOmega.lifted_polynomial ω
    (fun _ : Fin N → K => AugmentedGeneric.productMap g)
    (fun _ : Fin N → K => h) (fun x : Fin N → K => e.symm x)
    (isPolynomialFamily_const _) (fun _ => isPolynomialFamily_const _)
    (fun i => isPolynomialFamily_linear ((LinearMap.proj i).comp e.symm.toLinearMap))
  have hw : Function.Injective (AugmentedGenericOmega.lifted ω (AugmentedGeneric.productMap g)
      h (e.symm (e r₀))) := by
    rw [LinearEquiv.symm_apply_apply]
    exact AugmentedGenericOmega.lifted_injective_of_quotient ω _ _ _ hh hr₀
  obtain ⟨D,hD,hgood⟩ := injective_polynomial_principal_open
    (fun x : Fin N → K => AugmentedGenericOmega.lifted ω (AugmentedGeneric.productMap g) h (e.symm x))
    hpoly (e r₀) hw
  exact ⟨D,hD,fun x hx => AugmentedGenericOmega.quotient_injective_of_lifted ω _ _ _ (hgood x hx)⟩


end Quartic.SmallCovectorMotionOmega
