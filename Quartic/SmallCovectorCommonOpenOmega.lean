module

public import Quartic.SmallCovectorCommonOpen
public import Quartic.EndpointF13AllRangeOmega

@[expose] public section

/-! A common closed-covector coefficient open for the omega-marked block. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Quartic.SmallCovectorCommonOpenOmega
open Module MvPolynomial UniformEndpoint ProfileCertificate ConvolutionClosedSlices
open RowMultiplicationCoordinates HomogeneousCoefficientCoordinates
open BilinearCoefficientKernel BilinearCovectorCharts SmallCovectorCommonOpen
variable {K : Type*} [Field K] (ω : K)

/-- The closed covector sections and every checked block/F13/cubic condition
hold on one nonempty open, using identical mixed and child coefficients. -/
theorem common_open [IsAlgClosed K] (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40)
    (upper : Bool) (hω : ω ≠ 0) (hω1 : ω ≠ -1) :
    ∃ D : MvPolynomial (ParameterIndex m upper m (mixedCount m upper) (upperEndpoint m)) K,
      (∃ p,eval p D ≠ 0) ∧ ∀ p,eval p D ≠ 0 →
        SimultaneousBlockConditionsOmega.BlockConditions ω (baseProjection p) ∧
        GenericF13.Conditions (AugmentedGeneric.coefficientMixed (baseProjection p))
          (AugmentedGeneric.coefficientChild (baseProjection p)) ∧
        finrank K (CubicGeneric.CubicQuotient (AugmentedGeneric.coefficientChild (baseProjection p))) =
          (m+2).choose 3-m*upperEndpoint m ∧ ClosedConditions p := by
  classical
  obtain ⟨A,⟨a,ha⟩,hA⟩ := convolution_open (K := K) m hmlo hmhi upper
  obtain ⟨B,⟨b,hb⟩,hB⟩ := EndpointF13AllRangeOmega.generic_endpoint_conditions (K := K) ω m hmlo upper hω hω1
  let B' : MvPolynomial (ParameterIndex m upper m (mixedCount m upper) (upperEndpoint m)) K :=
    rename Sum.inl B
  have hA0 : A ≠ 0 := by intro h; simp [h] at ha
  have hB0 : B' ≠ 0 := by
    have he : eval (encode b 0) B' ≠ 0 := by
      simpa [B',eval_rename,encode,Function.comp_def] using hb
    intro h
    simp only [h,map_zero,ne_eq,not_true_eq_false] at he
  obtain ⟨p₀,hp₀⟩ := PolynomialImageAvoidance.exists_eval_ne_zero (mul_ne_zero hA0 hB0)
  refine ⟨A*B',⟨p₀,hp₀⟩,?_⟩
  intro p hp
  rw [map_mul,mul_ne_zero_iff] at hp
  have hb' : eval (baseProjection p) B ≠ 0 := by
    change eval (fun i => p (Sum.inl i)) B ≠ 0
    simpa only [B',eval_rename,Function.comp_def] using hp.2
  obtain ⟨hblock,hf13,hcubic⟩ := hB (baseProjection p) hb'
  exact ⟨hblock,hf13,hcubic,hA p hp.1⟩

/-- The common coefficient locus may be intersected with any prescribed
nonempty principal open on the full base coefficients. -/
theorem common_open_with [IsAlgClosed K] (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40)
    (upper : Bool) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (P : MvPolynomial (AugmentedGeneric.ParameterIndex m (mixedCount m upper) (upperEndpoint m)) K)
    (hP : ∃ a,eval a P≠0) :
    ∃ D : MvPolynomial (ParameterIndex m upper m (mixedCount m upper) (upperEndpoint m)) K,
      (∃ p,eval p D≠0) ∧ ∀ p,eval p D≠0 →
        eval (baseProjection p) P≠0 ∧
        SimultaneousBlockConditionsOmega.BlockConditions ω (baseProjection p) ∧
        GenericF13.Conditions (AugmentedGeneric.coefficientMixed (baseProjection p))
          (AugmentedGeneric.coefficientChild (baseProjection p)) ∧
        finrank K (CubicGeneric.CubicQuotient (AugmentedGeneric.coefficientChild (baseProjection p))) =
          (m+2).choose 3-m*upperEndpoint m ∧ ClosedConditions p := by
  classical
  obtain ⟨A,⟨a,ha⟩,hA⟩ := common_open ω m hmlo hmhi upper hω hω1
  obtain ⟨b,hb⟩ := hP
  let P' : MvPolynomial (ParameterIndex m upper m (mixedCount m upper) (upperEndpoint m)) K :=
    rename Sum.inl P
  have hA0 : A≠0 := by intro h;simpa [h] using ha
  have hP0 : P'≠0 := by
    have he : eval (encode b 0) P'≠0 := by
      simpa [P',eval_rename,encode,Function.comp_def] using hb
    intro h
    simpa only [h,map_zero,ne_eq,not_true_eq_false] using he
  obtain ⟨p₀,hp₀⟩ := PolynomialImageAvoidance.exists_eval_ne_zero (mul_ne_zero hA0 hP0)
  refine ⟨A*P',⟨p₀,hp₀⟩,?_⟩
  intro p hp
  rw [map_mul,mul_ne_zero_iff] at hp
  refine ⟨?_,hA p hp.1⟩
  change eval (fun i => p (Sum.inl i)) P≠0
  simpa only [P',eval_rename,Function.comp_def] using hp.2

end Quartic.SmallCovectorCommonOpenOmega
