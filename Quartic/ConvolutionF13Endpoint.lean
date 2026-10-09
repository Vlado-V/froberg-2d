module

public import Quartic.ConvolutionF13

@[expose] public section

/-!
# The actual F₁₃ conclusion at all canonical endpoints with m≥41

On the already constructed common coefficient open, the original convolution
presentation modulo Q is injective and has source, target, and cokernel
counts cα, 3β, and j. The mixed presentation remains fixed throughout.
-/
noncomputable section
namespace Quartic.ConvolutionF13Endpoint
open Module MvPolynomial PolynomialBilinearCoordinates
open ConvolutionF13 ConvolutionOuterGeneric ConvolutionOuterIncidence
open ConvolutionCubicGeneric ProfileCertificate UniformEndpoint
variable {K : Type*} [Field K]

/-- The actual F₁₃ source has the integer Euler count cα. -/
theorem source_finrank_eq_alpha (m : ℕ) (hm : 41 ≤ m) (upper : Bool)
    (Q : EndpointCoefficients K m upper) (hQ : LinearIndependent K Q) :
    (finrank K (ConvolutionF13.Source Q) : ℤ) =
      (mixedCount m upper : ℤ) * Counts.alpha m (upperEndpoint m) := by
  have hc := endpoint_columns_range m hm upper
  have hv := ConvolutionOuterGeneric.endpoint_variable_count m hm upper
  have hcols : coreP (mixedCount m upper) + 1 + 2 = mixedCount m upper := by
    unfold coreP
    omega
  have hbound : upperEndpoint m ≤ (m+1).choose 2 := by
    have h := Submodule.finrank_le (Submodule.span K (Set.range Q))
    rw [finrank_span_eq_card hQ, Fintype.card_fin] at h
    simpa only [Quartic.finrank_forms, hv, show m+2-1=m+1 by omega] using h
  have hd : finrank K (ConvolutionF13.Source Q) =
      mixedCount m upper * ((m+1).choose 2 - upperEndpoint m) := by
    calc
      _ = (coreP (mixedCount m upper)+1+2) *
          ((coreP (mixedCount m upper)+1+freeW m (mixedCount m upper)+1).choose 2 -
            upperEndpoint m) := ConvolutionF13.source_finrank Q hQ
      _ = _ := by rw [hv, hcols]
  rw [hd, Nat.cast_mul, Nat.cast_sub hbound]
  rfl

/-- Cubic independence gives the actual F₁₃ target count 3β. -/
theorem target_finrank_eq_beta (m : ℕ) (hm : 41 ≤ m) (upper : Bool)
    (Q : EndpointCoefficients K m upper)
    (hQ : Function.Injective (CubicGeneric.cubicMap Q)) :
    (finrank K (ConvolutionF13.Target Q) : ℤ) =
      3 * Counts.beta m (upperEndpoint m) := by
  have hv := ConvolutionOuterGeneric.endpoint_variable_count m hm upper
  have hd : finrank K (ConvolutionF13.Target Q) =
      3 * ((m+2).choose 3 - m * upperEndpoint m) := by
    calc
      _ = 3 * ((coreP (mixedCount m upper)+1+freeW m (mixedCount m upper)+2).choose 3 -
          (coreP (mixedCount m upper)+1+freeW m (mixedCount m upper))*upperEndpoint m) :=
        ConvolutionF13.target_finrank Q hQ
      _ = _ := by rw [hv]
  rw [hd, Nat.cast_mul, Nat.cast_sub (endpoint_cubic_budget m hm upper)]
  simp only [Counts.beta, Counts.b3, Nat.cast_mul, Nat.cast_ofNat]

/-- The actual reduced presentation has cokernel dimension exactly j. -/
theorem cokernel_finrank_eq_j (m : ℕ) (hm : 41 ≤ m) (upper : Bool)
    (Q : EndpointCoefficients K m upper) (hQ : CommonConditions m upper Q) :
    (finrank K (ConvolutionF13.Cokernel Q) : ℤ) =
      Counts.j m (upperEndpoint m) (mixedCount m upper) := by
  have hc := endpoint_columns_range m hm upper
  have ht : 2 ≤ coreP (mixedCount m upper)+1 := by unfold coreP; omega
  have h := cokernel_euler ht Q hQ.2.2.2.1
  have he : (finrank K (ConvolutionF13.Cokernel Q) : ℤ) +
      (finrank K (ConvolutionF13.Source Q) : ℤ) =
      (finrank K (ConvolutionF13.Target Q) : ℤ) := by exact_mod_cast h
  rw [source_finrank_eq_alpha m hm upper Q hQ.1,
    target_finrank_eq_beta m hm upper Q hQ.2.1] at he
  unfold Counts.j
  omega

/-- The common actual outer/cubic conditions together with the full fixed-presentation F₁₃ result. -/
def Conditions (m : ℕ) (upper : Bool) (Q : EndpointCoefficients K m upper) : Prop :=
  CommonConditions m upper Q ∧ Function.Injective (f13Map Q) ∧
    (finrank K (ConvolutionF13.Source Q) : ℤ) =
      (mixedCount m upper : ℤ) * Counts.alpha m (upperEndpoint m) ∧
    (finrank K (ConvolutionF13.Target Q) : ℤ) = 3 * Counts.beta m (upperEndpoint m) ∧
    (finrank K (ConvolutionF13.Cokernel Q) : ℤ) =
      Counts.j m (upperEndpoint m) (mixedCount m upper)

/-- A nonempty principal open of actual quadrics satisfies the concrete F₁₃ theorem. -/
theorem generic_conditions [Infinite K] (m : ℕ) (hm : 41 ≤ m) (upper : Bool) :
    ∃ P : MvPolynomial (Fin (finrank K (EndpointCoefficients K m upper))) K,
      (∃ Q : EndpointCoefficients K m upper,
        eval (coordinates K (EndpointCoefficients K m upper) Q) P ≠ 0) ∧
      ∀ Q : EndpointCoefficients K m upper,
        eval (coordinates K (EndpointCoefficients K m upper) Q) P ≠ 0 → Conditions m upper Q := by
  obtain ⟨P, hP, hgood⟩ := generic_common_conditions (K := K) m hm upper
  have hc := endpoint_columns_range m hm upper
  have ht : 2 ≤ coreP (mixedCount m upper)+1 := by unfold coreP; omega
  refine ⟨P, hP, fun Q hQ => ?_⟩
  have h := hgood Q hQ
  exact ⟨h, f13Map_injective ht Q h.2.2.2.1,
    source_finrank_eq_alpha m hm upper Q h.1,
    target_finrank_eq_beta m hm upper Q h.2.1, cokernel_finrank_eq_j m hm upper Q h⟩

/-- In particular, such a concrete quadratic tuple exists over every infinite field. -/
theorem exists_conditions [Infinite K] (m : ℕ) (hm : 41 ≤ m) (upper : Bool) :
    ∃ Q : EndpointCoefficients K m upper, Conditions m upper Q := by
  obtain ⟨P, ⟨Q, hQ⟩, hgood⟩ := generic_conditions (K := K) m hm upper
  exact ⟨Q, hgood Q hQ⟩

end Quartic.ConvolutionF13Endpoint
