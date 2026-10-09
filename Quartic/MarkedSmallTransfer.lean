module

public import Quartic.MarkedEndpointFlag
public import Quartic.MarkedEndpointBudget
public import Quartic.MarkedSquareGenericOmega
public import Quartic.ActualMarkedSmallResponseRankOmega
public import Quartic.MarkedParentWitness

@[expose] public section

/-! The small-range three-variable transfer retains an actual parent square.
The child flag, fixed marked square and covector conditions are imposed on
one common coefficient point before any response motion is selected. -/
noncomputable section
namespace Quartic.MarkedSmallTransfer
open Module MvPolynomial UniformEndpoint SmallCovectorCommonOpen
open ActualMarkedSmallMotionAvoidanceOmega ActualDeformationResponseOmega ActualDeformationColumnsOmega
variable {K : Type*} [Field K] [Infinite K] [IsAlgClosed K]
variable (ω : K)
set_option maxHeartbeats 1800000

/-- The canonical marked child space and the enlarged response are realized
at the same actual mixed/child coefficient point. -/
theorem exists_data (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40) (upper : Bool)
    (hω : ω ≠ 0) (hω1 : ω ≠ -1) (hchild : MarkedEndpoints K m) :
    ∃ p : Parameters K m upper, ∃ k : Fin (upperEndpoint m),
      ∃ ζ : MiddleCoordinates.Mixed K m,
      ∃ r : Fin 4 → Forms K m 2, ∃ s : Fin (mixedCount m upper) → Forms K m 2,
      SimultaneousBlockConditionsOmega.BlockConditions ω (baseProjection p) ∧
      GenericF13.Conditions (G p) (Q p) ∧
      Function.Surjective (quadraticMultiplication (Q p)) ∧
      (finrank K (childMarkedCoefficient (Q p) k).range : ℤ) =
        Counts.delta m (upperEndpoint m) ∧
      (finrank K (ActualMarkedSquareResponseOmega.response ω (G p) (Q p) r
        (ExtraCorrectionOmega.squareClass (Q p) ζ)
        (childMarkedCoefficient (Q p) k).range s).range : ℤ) =
        min (((2*m+2*mixedCount m upper : ℕ) : ℤ) +
          Counts.H m (upperEndpoint m) (mixedCount m upper) + 4 +
          finrank K (childMarkedCoefficient (Q p) k).range)
          (Counts.j m (upperEndpoint m) (mixedCount m upper)) := by
  classical
  obtain ⟨hc,hbudget⟩ := MarkedEndpointBudget.block_budgets m hmlo upper
  let ζ : MiddleCoordinates.Mixed K m := MarkedSquareEmbedding.zeta hc
  have hpoly : IsPolynomialFamily
      (AugmentedGeneric.coefficientChild (K := K) (m := m)
        (c := mixedCount m upper) (q := upperEndpoint m)) :=
    isPolynomialFamily_linear AugmentedGeneric.coefficientChild
  have hsurj : Function.Surjective
      (AugmentedGeneric.coefficientChild (K := K) (m := m)
        (c := mixedCount m upper) (q := upperEndpoint m)) := by
    intro h
    exact ⟨AugmentedGeneric.encode 0 h 0, AugmentedGeneric.coefficientChild_encode 0 h 0⟩
  obtain ⟨A,⟨a,ha⟩,hA⟩ := MarkedEndpointFlag.principal_open (by omega : 1 ≤ m)
    (upperEndpoint m) rfl AugmentedGeneric.coefficientChild hpoly hsurj hchild
  obtain ⟨B,⟨b,hb⟩,hB⟩ :=
    MarkedSquareGenericOmega.genericMarkedAugmented_of_budget (K := K) ω hω hω1 hc hbudget
  have hA0 : A ≠ 0 := by intro hz; simp [hz] at ha
  have hB0 : B ≠ 0 := by intro hz; simp [hz] at hb
  obtain ⟨ab,hab⟩ := PolynomialImageAvoidance.exists_eval_ne_zero (mul_ne_zero hA0 hB0)
  let extra := fun a : AugmentedGeneric.ParameterIndex m (mixedCount m upper) (upperEndpoint m) → K =>
    ExtraCorrectionOmega.squareClass (AugmentedGeneric.coefficientChild a) ζ
  have hExtra : ∀ a, eval a (A*B) ≠ 0 → Function.Injective
      (ExtraCorrectionOmega.augmented ω (AugmentedGeneric.coefficientMixed a)
        (AugmentedGeneric.coefficientChild a) (AugmentedGeneric.coefficientMotions a) (extra a)) := by
    intro a ha
    rw [map_mul,mul_ne_zero_iff] at ha
    change Function.Injective (ExtraCorrectionOmega.augmented ω _ _ _
      (ExtraCorrectionOmega.squareClass _ ζ))
    rw [ExtraCorrectionOmega.augmented_square_eq]
    exact (hB a ha.2).2.2
  obtain ⟨p,hP,hblock,hf13,_,hresponse⟩ :=
    ActualMarkedSmallResponseRankOmega.exists_common_maximal_response_with (K := K)
      ω m hmlo hmhi upper hω hω1 extra (A*B) ⟨ab,hab⟩ hExtra
  rw [map_mul,mul_ne_zero_iff] at hP
  obtain ⟨_,hchildSurj,k,hk⟩ := hA (baseProjection p) hP.1
  let U := (childMarkedCoefficient (Q p) k).range
  obtain ⟨r,s,haug,hrank⟩ := hresponse U
  refine ⟨p,k,ζ,r,s,hblock,hf13,hchildSurj,hk,?_⟩
  have hsource := ActualMarkedSquareResponseOmega.source_finrank ω (G p) (Q p) r
    (extra (baseProjection p)) U hblock.1.1 hblock.1.2.1 haug hblock.1.2.2.1
  have hj := ActualSplitCokernel.rawJ_finrank_eq_j (G p) (Q p)
    hf13.1 hf13.2.1 hf13.2.2
  change (finrank K (ActualMarkedSquareResponseOmega.response ω (G p) (Q p) r
    (extra (baseProjection p)) U s).range : ℤ) = _
  rw [hrank,Nat.cast_min,hsource,hj]

private theorem parent_count (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    4+(mixedCount m upper+upperEndpoint m)=parentCount m upper := by
  have hc := (EndpointBlockConditions.structural_counts m hm upper).1
  unfold mixedCount at hc ⊢
  omega

/-- Positive lower surplus retains a parent square after the exact response. -/
theorem lower_parent_witness (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40)
    (hω : ω ≠ 0) (hω1 : ω ≠ -1) (hchild : MarkedEndpoints K m)
    (hpos : 0 < Counts.chi (m+3) (lowerEndpoint (m+3))) :
    MarkedLowerWitness K (m+3) (lowerEndpoint (m+3)) := by
  obtain ⟨p,k,ζ,r,s,hblock,hf13,hchildSurj,hdim,hresponse⟩ :=
    exists_data ω m hmlo hmhi false hω hω1 hchild
  have hp : 0 < Counts.chi (3+m) (4+(mixedCount m false+upperEndpoint m)) := by
    simpa only [parent_count m hmlo false,parentCount,Bool.false_eq_true,ite_false,
      Nat.add_comm 3 m] using hpos
  have hw := MarkedParentWitness.of_response_formula ω (G p) (Q p) s r k ζ
    (childMarkedCoefficient (Q p) k).range (canonical_marked_representatives (Q p) k)
    hblock.1.1 hblock.1.2.1 hblock.1.2.2.1 hchildSurj hf13.2.1 hf13.2.2
    hdim hp hresponse
  simpa only [parent_count m hmlo false,parentCount,Bool.false_eq_true,ite_false,
    Nat.add_comm 3 m] using hw

/-- The pencil parameter is chosen internally over the infinite field. -/
theorem lower_witness (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40)
    (hchild : MarkedEndpoints K m)
    (hpos : 0 < Counts.chi (m+3) (lowerEndpoint (m+3))) :
    MarkedLowerWitness K (m+3) (lowerEndpoint (m+3)) := by
  obtain ⟨ω,hω,hω1⟩ := ThreeBlockOmega.exists_parameter (K := K)
  exact lower_parent_witness ω m hmlo hmhi hω hω1 hchild hpos

end Quartic.MarkedSmallTransfer
