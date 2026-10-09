module

public import Quartic.ConvolutionSmallOuter
public import Quartic.ConvolutionCubicGeneric

@[expose] public section

/-!
# The common actual cubic and outer conditions throughout m≥28

The finite profile-chart argument extends the outer open to the remaining
small endpoint configurations. All count identities and the common ordinary
cubic open therefore hold over the whole child range.
-/
noncomputable section
namespace Quartic.ConvolutionAllRange
open Module MvPolynomial ConvolutionFreePieces ConvolutionFreeMultiplication
open ConvolutionOuterIncidence ConvolutionOuterGeneric ConvolutionCubicGeneric
open ProfileCertificate UniformEndpoint PolynomialBilinearCoordinates
variable {K : Type*} [Field K]

theorem endpoint_source_finrank (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    finrank K (Piece K (coreP (mixedCount m upper)+1)
      (freeW m (mixedCount m upper)) 1)=totalA m (mixedCount m upper) := by
  exact source_finrank _ (EndpointBlockConditions.structural_counts m hm upper).1 _

/-- All endpoint column counts lie in the range of the actual convolution model. -/
theorem endpoint_columns_range (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    4 ≤ mixedCount m upper ∧ mixedCount m upper ≤ m := by
  by_cases hsmall : m ≤ 319
  · have h := (FiniteCounts.structural_binomial_counts m (by omega) hsmall upper)
    simp only [mixedCount_eq_table m hsmall]
    exact ⟨h.1, h.2.1⟩
  · exact UniformScalar.c_range m (by omega) upper

/-- The core and free variables together are exactly the ambient child variables. -/
theorem endpoint_variable_count (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    coreP (mixedCount m upper) + 1 + freeW m (mixedCount m upper) = m := by
  have hc := endpoint_columns_range m hm upper
  unfold coreP freeW
  omega

/-- The actual cubic target has the source Euler count T, at every canonical endpoint. -/
theorem endpoint_target_euler (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    (finrank K (Piece K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) 3) : ℤ) =
        UniformScalar.targetCount m (mixedCount m upper) := by
  have hc := endpoint_columns_range m hm upper
  have ht : 2 ≤ coreP (mixedCount m upper) + 1 := by unfold coreP; omega
  have hvars : coreP (mixedCount m upper) + 1 + freeW m (mixedCount m upper) = m := by
    unfold coreP freeW
    omega
  have hcols : coreP (mixedCount m upper) + 1 + 2 = mixedCount m upper := by
    unfold coreP
    omega
  have h := ConvolutionFree.degreeThree_euler (K := K)
    (w := freeW m (mixedCount m upper)) ht
  have hh : finrank K (ConvolutionFree.Cokernel K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) 2) +
      mixedCount m upper * (m + 1).choose 2 = 3 * (m + 2).choose 3 := by
    simpa only [hvars, hcols] using h
  have he : (finrank K (ConvolutionFree.Cokernel K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) 2) : ℤ) +
      (mixedCount m upper : ℤ) * ((m + 1).choose 2 : ℤ) = 3 * ((m + 2).choose 3 : ℤ) := by
    exact_mod_cast hh
  rw [(pieceSuccEquiv (K := K) (t := coreP (mixedCount m upper) + 1)
    (w := freeW m (mixedCount m upper)) (j := 2)).finrank_eq]
  unfold UniformScalar.targetCount Counts.b2 Counts.b3
  omega

/-- Every injective endpoint outer map has quotient dimension exactly j=T−qa. -/
theorem endpoint_quotient_finrank_eq_j (m : ℕ) (hm : 28 ≤ m) (upper : Bool)
    (Q : EndpointCoefficients K m upper) (hQ : Function.Injective (outerMap Q)) :
    (finrank K (OuterQuotient Q) : ℤ) =
      Counts.j m (upperEndpoint m) (mixedCount m upper) := by
  have hc := endpoint_columns_range m hm upper
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range (outerMap Q))
  rw [LinearMap.finrank_range_of_inj hQ] at h
  have hs : finrank K (SourceTuple K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) (upperEndpoint m)) =
      upperEndpoint m * totalA m (mixedCount m upper) := by
    calc
      _ = ∑ j : Fin (upperEndpoint m), finrank K (Piece K (coreP (mixedCount m upper) + 1)
          (freeW m (mixedCount m upper)) 1) := Module.finrank_pi_fintype K
      _ = _ := by simp [endpoint_source_finrank m hm upper]
  rw [hs] at h
  have he : (finrank K (OuterQuotient Q) : ℤ) +
      (upperEndpoint m : ℤ) * (totalA m (mixedCount m upper) : ℤ) =
      (finrank K (Piece K (coreP (mixedCount m upper) + 1)
        (freeW m (mixedCount m upper)) 3) : ℤ) := by exact_mod_cast h
  rw [endpoint_target_euler m hm upper, totalA_eq m _ hc.1 hc.2,
    Nat.cast_sub (by omega : mixedCount m upper ≤ 3 * m)] at he
  push_cast at he
  unfold UniformScalar.targetCount Counts.j Counts.beta Counts.alpha at *
  nlinarith

/-- One nonempty principal open simultaneously gives independent actual
quadrics, injective outer multiplication, and the exact outer quotient count. -/
theorem generic_outer_exact [Infinite K] (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    ∃ P : MvPolynomial (Fin (finrank K (EndpointCoefficients K m upper))) K,
      (∃ Q : EndpointCoefficients K m upper,
        eval (coordinates K (EndpointCoefficients K m upper) Q) P ≠ 0) ∧
      ∀ Q : EndpointCoefficients K m upper,
        eval (coordinates K (EndpointCoefficients K m upper) Q) P ≠ 0 →
          LinearIndependent K Q ∧ Function.Injective (outerMap Q) ∧
          (finrank K (OuterQuotient Q) : ℤ) =
            Counts.j m (upperEndpoint m) (mixedCount m upper) := by
  obtain ⟨P, hP, hgood⟩ := ConvolutionSmallOuter.generic_outer_injective (K := K) m hm upper
  have hc := endpoint_columns_range m hm upper
  have ht : 2 ≤ coreP (mixedCount m upper) + 1 := by unfold coreP; omega
  refine ⟨P, hP, ?_⟩
  intro Q hQ
  have hi := hgood Q hQ
  exact ⟨independent_of_outer_injective ht Q hi, hi, endpoint_quotient_finrank_eq_j m hm upper Q hi⟩

/-- An actual independent quadratic tuple with injective outer multiplication
and the exact quotient count exists at every canonical endpoint. -/
theorem exists_outer_exact [Infinite K] (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    ∃ Q : EndpointCoefficients K m upper,
      LinearIndependent K Q ∧ Function.Injective (outerMap Q) ∧
      (finrank K (OuterQuotient Q) : ℤ) =
        Counts.j m (upperEndpoint m) (mixedCount m upper) := by
  obtain ⟨P, ⟨Q, hQ⟩, hgood⟩ := generic_outer_exact (K := K) m hm upper
  exact ⟨Q, hgood Q hQ⟩

/-- The source cubic budget holds at every canonical endpoint. -/
theorem endpoint_cubic_budget (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    m * upperEndpoint m ≤ (m + 2).choose 3 := by
  have h := (EndpointBlockConditions.structural_counts m (by omega) upper).2.2.1
  unfold Counts.b3 at h
  exact_mod_cast h

/-- A shared nonempty principal open for both actual cubic multiplication maps. -/
theorem generic_common_conditions [Infinite K] (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
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
theorem exists_common_conditions [Infinite K] (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    ∃ Q : EndpointCoefficients K m upper, CommonConditions m upper Q := by
  obtain ⟨P, ⟨Q, hQ⟩, hgood⟩ := generic_common_conditions (K := K) m hm upper
  exact ⟨Q, hgood Q hQ⟩

/-- The ordinary cubic quotient has the manuscript's integer count β on the same open. -/
theorem cubic_quotient_eq_beta (m : ℕ) (hm : 28 ≤ m) (upper : Bool)
    (Q : EndpointCoefficients K m upper) (hQ : CommonConditions m upper Q) :
    (finrank K (CubicGeneric.CubicQuotient Q) : ℤ) = Counts.beta m (upperEndpoint m) := by
  rw [hQ.2.2.1, Nat.cast_sub (endpoint_cubic_budget m hm upper)]
  simp only [Counts.beta, Counts.b3, Nat.cast_mul]

end Quartic.ConvolutionAllRange
