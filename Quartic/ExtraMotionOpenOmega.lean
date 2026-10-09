module

public import Quartic.ExtraCorrectionOmega
public import Quartic.PolynomialRankOpen

@[expose] public section

/-! The augmented good locus remains a principal open while pure motions vary,
with an arbitrary fixed extra target column. -/
noncomputable section
namespace Quartic.ExtraMotionOpenOmega
open Module MvPolynomial HomologyCoordinates
variable {K : Type*} [Field K] (ω : K)

theorem augmented_polynomial {ι S A : Type*}
    [AddCommGroup S] [Module K S] [FiniteDimensional K S]
    [AddCommGroup A] [Module K A] [FiniteDimensional K A]
    (F : (ι → K) → (S →ₗ[K] A × A)) (r : (ι → K) → Fin 4 → A)
    (hF : IsPolynomialFamily F) (hr : ∀ i,IsPolynomialFamily (fun x => r x i)) :
    IsPolynomialFamily (fun x => AugmentedGenericOmega.augmented ω (F x) (r x)) := by
  apply isPolynomialFamily_linearMap
  rintro ⟨b,a,ξ⟩
  have hp := hF.linear_comp (LinearMap.applyₗ (R := K) (M₂ := A × A) b)
  have ht₁ := IsPolynomialFamily.sum (fun i : Fin 4 =>
    (isPolynomialFamily_const (ι := ι) (homologyReduction ξ i).1).smul (hr i))
  have ht₂ := IsPolynomialFamily.sum (fun i : Fin 4 =>
    (isPolynomialFamily_const (ι := ι) (homologyReduction ξ i).2).smul (hr i))
  have hall := (hp.add (isPolynomialFamily_const (ι := ι) (ω • a,-a))).add (ht₁.prod_mk ht₂)
  simpa [AugmentedGenericOmega.augmented,AugmentedMiddle.pureTrace,add_assoc] using hall

theorem augmented_motion_open {m c q N : ℕ}
    (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2)
    (extra : ExtraCorrectionOmega.ChildQuotient h × ExtraCorrectionOmega.ChildQuotient h)
    (e : (Fin 4 → Forms K m 2) ≃ₗ[K] (Fin N → K))
    (r₀ : Fin 4 → Forms K m 2)
    (hr₀ : Function.Injective (ExtraCorrectionOmega.augmented ω g h r₀ extra)) :
    ∃ D : MvPolynomial (Fin N) K,eval (e r₀) D≠0 ∧ ∀ x,eval x D≠0 →
      Function.Injective (ExtraCorrectionOmega.augmented ω g h (e.symm x) extra) := by
  classical
  let Q := Submodule.span K (Set.range h)
  have hpoly := augmented_polynomial ω
    (fun _ : Fin N → K => ExtraTraceOmega.withColumn
      (MovingMiddleCorrectionOmega.quotientProduct g Q) extra)
    (fun x : Fin N → K => fun i => Q.mkQ (e.symm x i))
    (isPolynomialFamily_const _) (fun i =>
      isPolynomialFamily_linear (Q.mkQ.comp ((LinearMap.proj i).comp e.symm.toLinearMap)))
  have hw : Function.Injective (ExtraCorrectionOmega.augmented ω g h (e.symm (e r₀)) extra) := by
    simpa only [LinearEquiv.symm_apply_apply] using hr₀
  exact injective_polynomial_principal_open
    (fun x : Fin N → K => ExtraCorrectionOmega.augmented ω g h (e.symm x) extra)
    hpoly (e r₀) hw

end Quartic.ExtraMotionOpenOmega
