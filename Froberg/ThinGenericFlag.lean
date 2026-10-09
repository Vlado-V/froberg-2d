module

public import Froberg.ThinQuotientStrata
public import Froberg.GenericFlagOpen

@[expose] public section

/-! The actual thin scalar quotient and both levels of a generic child flag
hold on the same nonempty open of scalar coefficients. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial Quartic.PolynomialBilinearCoordinates
open BilinearScalarFamily
variable {K V W : Type*} [Field K] [Infinite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {n d r q j : ℕ} {C : ℝ}

theorem thin_quotient_coefficient_open (mu : Forms K n d →ₗ[K] V →ₗ[K] W)
    (hthin : HasThinQuotientOpen mu q j C) :
    ∃ P : MvPolynomial (CoefficientIndex n d q) K,
      (∃ a,eval a P ≠ 0) ∧ ∀ a,eval a P ≠ 0 →
        Function.Injective (multiplication mu (coefficientForms K n d q a)) ∧
        finrank K (ScalarQuotient mu (coefficientForms K n d q a))=j ∧
        HasClosedKernelSlices (scalarQuotientBilinear mu (coefficientForms K n d q a))
          (BilinearCovectorStrata.thinSlices j C) := by
  classical
  obtain ⟨P,⟨Q₀,hQ₀⟩,hgood⟩ := hthin
  let dec := (coefficientCoordinates (K := K) (n := n) (d := d) (r := q)).symm.toLinearMap
  let L : (CoefficientIndex n d q → K) →ₗ[K] ((Fin q × Fin (finrank K (Forms K n d))) → K) :=
    LinearMap.pi (fun ik => (LinearMap.proj ik.2).comp
      ((coordinates K (Forms K n d)).toLinearMap.comp ((LinearMap.proj ik.1).comp dec)))
  let P' := Quartic.MiddleCoordinates.substituteLinear L P
  have hev (a : CoefficientIndex n d q → K) :
      eval a P'=eval (fun ik => coordinates K _ (coefficientForms K n d q a ik.1) ik.2) P := by
    dsimp only [P']
    rw [Quartic.MiddleCoordinates.eval_substituteLinear]
    rfl
  refine ⟨P',?_,fun a ha => hgood _ ((hev a) ▸ ha)⟩
  refine ⟨coefficientCoordinates Q₀,?_⟩
  rw [hev]
  have he : coefficientForms K n d q (coefficientCoordinates Q₀)=Q₀ :=
    coefficientCoordinates.symm_apply_apply Q₀
  simpa only [he] using hQ₀

theorem thin_generic_flag_principal_open (mu : Forms K n d →ₗ[K] V →ₗ[K] W)
    (hn : 0 < n) (hrq : r ≤ q) (hq : q ≤ (n+d-1).choose d)
    (hthin : HasThinQuotientOpen mu q j C) :
    ∃ P : MvPolynomial (CoefficientIndex n d q) K,
      (∃ a,eval a P ≠ 0) ∧ ∀ a,eval a P ≠ 0 →
        LinearIndependent K (coefficientForms K n d q a) ∧
        coefficientCokernel K n d q a=genericCokernel K n d q ∧
        finrank K (EndpointHomology (coefficientForms K n d q a ∘ Fin.castLE hrq))=
          genericHomology K n d r ∧
        Function.Injective (multiplication mu (coefficientForms K n d q a)) ∧
        finrank K (ScalarQuotient mu (coefficientForms K n d q a))=j ∧
        HasClosedKernelSlices (scalarQuotientBilinear mu (coefficientForms K n d q a))
          (BilinearCovectorStrata.thinSlices j C) := by
  obtain ⟨D,hD,hd⟩ := thin_quotient_coefficient_open mu hthin
  obtain ⟨E,hE,he⟩ := generic_flag_principal_open (K := K) hn hrq hq
  obtain ⟨a,haD,haE⟩ := principal_opens_intersect hD hE
  refine ⟨D*E,⟨a,by simpa only [map_mul] using mul_ne_zero haD haE⟩,?_⟩
  intro a ha
  obtain ⟨haD,haE⟩ := mul_ne_zero_iff.mp (show eval a D*eval a E ≠ 0 by simpa only [map_mul] using ha)
  have hflag := he a haE
  exact ⟨hflag.1,hflag.2.1,hflag.2.2.2,hd a haD⟩

end Froberg
