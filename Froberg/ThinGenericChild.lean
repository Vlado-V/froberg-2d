import Froberg.ThinQuotientStrata
import Froberg.GenericDimensions

/-! A thin scalar open is compatible with an actual generic child family. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Quartic.PolynomialBilinearCoordinates
open BilinearScalarFamily
variable {K V W : Type*} [Field K] [Infinite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {n d q j : ℕ} {C : ℝ}

theorem exists_thin_generic_child (mu : Forms K n d →ₗ[K] V →ₗ[K] W)
    (hn : 0 < n) (hq : q ≤ (n+d-1).choose d) (hthin : HasThinQuotientOpen mu q j C) :
    ∃ Q : Fin q → Forms K n d,
      LinearIndependent K Q ∧
      finrank K (EndpointHomology Q)=genericHomology K n d q ∧
      finrank K (EndpointQuotient K n d (Submodule.span K (Set.range (fun i => (Q i).val))))=
        genericCokernel K n d q ∧
      Function.Injective (BilinearScalarFamily.multiplication mu Q) ∧
      finrank K (ScalarQuotient mu Q)=j ∧
      HasClosedKernelSlices (scalarQuotientBilinear mu Q) (BilinearCovectorStrata.thinSlices j C) := by
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
  have hP' : ∃ a,eval a P' ≠ 0 := by
    refine ⟨coefficientCoordinates Q₀,?_⟩
    rw [hev]
    have he : coefficientForms K n d q (coefficientCoordinates Q₀)=Q₀ :=
      coefficientCoordinates.symm_apply_apply Q₀
    simpa only [he] using hQ₀
  obtain ⟨D,hD,hgeneric⟩ := genericCokernel_principal_open K n d q hn
  obtain ⟨E,hE,hind⟩ := coefficient_independence_principal_open (K := K) hn hq
  obtain ⟨a₀,haD,haE⟩ := principal_opens_intersect hD hE
  have hDE : ∃ a,eval a (D*E) ≠ 0 := ⟨a₀,by simpa only [map_mul] using mul_ne_zero haD haE⟩
  obtain ⟨a,haP,haDE⟩ := principal_opens_intersect hP' hDE
  have hi := hind a ((mul_ne_zero_iff.mp (by simpa only [map_mul] using haDE)).2)
  have hc := hgeneric a ((mul_ne_zero_iff.mp (by simpa only [map_mul] using haDE)).1)
  refine ⟨coefficientForms K n d q a,hi,(genericHomology_eq_at_generic hn a hi hc).symm,hc,?_⟩
  exact hgood _ ((hev a) ▸ haP)

end Froberg
