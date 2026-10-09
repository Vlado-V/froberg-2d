module

public import Quartic.ExpansionCommonOpen
public import Quartic.EndpointF13AllRangeOmega

@[expose] public section

/-! Ordinary expansion and the modified pencil on one coefficient open. -/
noncomputable section
namespace Quartic.ExpansionCommonOpenOmega
open Module MvPolynomial RowMultiplicationCoordinates RowExpansionOpen
open UniformEndpoint ProfileCertificate
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]

include L in
theorem common_open [Infinite K] (ω : K) (m : ℕ) (hm : 41 ≤ m) (upper : Bool) (hω : ω ≠ 0) (hω1 : ω ≠ -1) :
    ∃ E : ConvolutionExpansionOpen.Dimensions m upper → ℕ,
      ConvolutionExpansionOpen.Thresholds m upper E ∧
      ∃ D : MvPolynomial (AugmentedGeneric.ParameterIndex m (mixedCount m upper) (upperEndpoint m)) K,
        (∃ p, eval p D ≠ 0) ∧ ∀ p, eval p D ≠ 0 →
          SimultaneousBlockConditionsOmega.BlockConditions ω p ∧
          GenericF13.Conditions (AugmentedGeneric.coefficientMixed p) (AugmentedGeneric.coefficientChild p) ∧
          finrank K (CubicGeneric.CubicQuotient (AugmentedGeneric.coefficientChild p)) =
            (m+2).choose 3-m*upperEndpoint m ∧
          ∀ d : ConvolutionExpansionOpen.Dimensions m upper,
            RowExpansionOpen.Expands (AugmentedGeneric.coefficientMixed p)
              (d.val+mixedCount m upper) (E d+mixedCount m upper*(m+1).choose 2) := by
  classical
  obtain ⟨E,hE,A,⟨a,ha⟩,hA⟩ := ExpansionCommonOpen.expansion_augmented (K := K) (L := L) m hm upper
  obtain ⟨B,⟨b,hb⟩,hB⟩ := EndpointF13AllRangeOmega.generic_endpoint_conditions (K := K) ω m (by omega) upper hω hω1
  have hA0 : A ≠ 0 := by intro h; simp [h] at ha
  have hB0 : B ≠ 0 := by intro h; simp [h] at hb
  obtain ⟨p₀,hp₀⟩ := nonempty_principal_intersection
    (![A,B] : Fin 2 → MvPolynomial
      (AugmentedGeneric.ParameterIndex m (mixedCount m upper) (upperEndpoint m)) K)
    (by intro i; fin_cases i <;> assumption)
  refine ⟨E,hE,A*B,⟨p₀,?_⟩,?_⟩
  · rw [map_mul]
    exact mul_ne_zero (hp₀ 0) (hp₀ 1)
  · intro p hp
    rw [map_mul,mul_ne_zero_iff] at hp
    obtain ⟨hb,hf,hc⟩ := hB p hp.2
    exact ⟨hb,hf,hc,hA p hp.1⟩

end Quartic.ExpansionCommonOpenOmega

