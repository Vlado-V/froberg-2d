module

public import Quartic.CubicGeneric
public import Quartic.ConvolutionOuterGeneric
public import Quartic.EndpointBlockConditions

@[expose] public section

/-!
# One actual quadratic family for ordinary and outer cubic multiplication

At either canonical endpoint in every child dimension `m ≥ 41`, a nonempty
principal open in the same actual quadratic coefficient space satisfies both
the ordinary cubic lemma and injectivity of the outer convolution map. The
convolution presentation remains fixed; this does not claim genericity as
that presentation varies or an assembled split-complex theorem.
-/

noncomputable section
namespace Quartic.ConvolutionCubicGeneric
open Module MvPolynomial PolynomialBilinearCoordinates
open ConvolutionOuterGeneric ConvolutionOuterIncidence ProfileCertificate UniformEndpoint
variable {K : Type*} [Field K]

/-- The canonical convolution variables comprise exactly the child variables. -/
theorem endpoint_variable_count (m : ℕ) (hm : 41 ≤ m) (upper : Bool) :
    coreP (mixedCount m upper) + 1 + freeW m (mixedCount m upper) = m := by
  have hc := endpoint_columns_range m hm upper
  unfold coreP freeW
  omega

/-- The source cubic budget holds at every canonical endpoint. -/
theorem endpoint_cubic_budget (m : ℕ) (hm : 41 ≤ m) (upper : Bool) :
    m * upperEndpoint m ≤ (m + 2).choose 3 := by
  have h := (EndpointBlockConditions.structural_counts m (by omega) upper).2.2.1
  unfold Counts.b3 at h
  exact_mod_cast h

/-- The same actual child quadrics satisfy the ordinary and outer cubic conclusions. -/
def CommonConditions (m : ℕ) (upper : Bool) (Q : EndpointCoefficients K m upper) : Prop :=
  LinearIndependent K Q ∧
    Function.Injective (CubicGeneric.cubicMap Q) ∧
    finrank K (CubicGeneric.CubicQuotient Q) =
      (m + 2).choose 3 - m * upperEndpoint m ∧
    Function.Injective (outerMap Q) ∧
    (finrank K (OuterQuotient Q) : ℤ) =
      Counts.j m (upperEndpoint m) (mixedCount m upper)

/-- A shared nonempty principal open for both actual cubic multiplication maps. -/
theorem generic_common_conditions [Infinite K] (m : ℕ) (hm : 41 ≤ m) (upper : Bool) :
    ∃ P : MvPolynomial (Fin (finrank K (EndpointCoefficients K m upper))) K,
      (∃ Q : EndpointCoefficients K m upper,
        eval (coordinates K (EndpointCoefficients K m upper) Q) P ≠ 0) ∧
      ∀ Q : EndpointCoefficients K m upper,
        eval (coordinates K (EndpointCoefficients K m upper) Q) P ≠ 0 →
          CommonConditions m upper Q := by
  classical
  have hvars := endpoint_variable_count m hm upper
  have hdim : 3 ≤ coreP (mixedCount m upper) + 1 + freeW m (mixedCount m upper) := by
    omega
  have hbudget : (coreP (mixedCount m upper) + 1 + freeW m (mixedCount m upper)) *
      upperEndpoint m ≤
      (coreP (mixedCount m upper) + 1 + freeW m (mixedCount m upper) + 2).choose 3 := by
    rw [hvars]
    exact endpoint_cubic_budget m hm upper
  obtain ⟨Pc, ⟨Qc, hQc⟩, hc⟩ := CubicGeneric.generic_cubic_independence (K := K) hdim hbudget
  obtain ⟨Po, ⟨Qo, hQo⟩, ho⟩ := generic_outer_exact (K := K) m hm upper
  have hPc : Pc ≠ 0 := by intro h; simp [h] at hQc
  have hPo : Po ≠ 0 := by intro h; simp [h] at hQo
  obtain ⟨a, ha⟩ := nonempty_principal_intersection
    (![Pc, Po] : Fin 2 → MvPolynomial (Fin (finrank K (EndpointCoefficients K m upper))) K)
    (by intro i; fin_cases i <;> assumption)
  refine ⟨Pc * Po, ⟨(coordinates K (EndpointCoefficients K m upper)).symm a, ?_⟩, ?_⟩
  · simp only [LinearEquiv.apply_symm_apply, map_mul]
    exact mul_ne_zero (ha 0) (ha 1)
  · intro Q hQ
    rw [map_mul] at hQ
    obtain ⟨hQc, hQo⟩ := mul_ne_zero_iff.mp hQ
    obtain ⟨hlin, hci, hcd⟩ := hc Q hQc
    obtain ⟨_, hoi, hod⟩ := ho Q hQo
    refine ⟨hlin, hci, ?_, hoi, hod⟩
    calc
      finrank K (CubicGeneric.CubicQuotient Q) =
        (coreP (mixedCount m upper) + 1 + freeW m (mixedCount m upper) + 2).choose 3 -
          (coreP (mixedCount m upper) + 1 + freeW m (mixedCount m upper)) * upperEndpoint m := hcd
      _ = _ := by rw [hvars]

/-- Existence of one actual quadratic tuple satisfying all the shared conditions. -/
theorem exists_common_conditions [Infinite K] (m : ℕ) (hm : 41 ≤ m) (upper : Bool) :
    ∃ Q : EndpointCoefficients K m upper, CommonConditions m upper Q := by
  obtain ⟨P, ⟨Q, hQ⟩, hgood⟩ := generic_common_conditions (K := K) m hm upper
  exact ⟨Q, hgood Q hQ⟩

/-- The ordinary cubic quotient has the manuscript's integer count β on the same open. -/
theorem cubic_quotient_eq_beta (m : ℕ) (hm : 41 ≤ m) (upper : Bool)
    (Q : EndpointCoefficients K m upper) (hQ : CommonConditions m upper Q) :
    (finrank K (CubicGeneric.CubicQuotient Q) : ℤ) = Counts.beta m (upperEndpoint m) := by
  rw [hQ.2.2.1, Nat.cast_sub (endpoint_cubic_budget m hm upper)]
  simp only [Counts.beta, Counts.b3, Nat.cast_mul]

end Quartic.ConvolutionCubicGeneric
