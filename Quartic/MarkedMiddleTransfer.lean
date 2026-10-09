module

public import Quartic.MarkedEndpointBudget
public import Quartic.MarkedEndpointFlag
public import Quartic.MarkedExpansionCommonOpenOmega
public import Quartic.MarkedExpansionMotionBridgeOmega
public import Quartic.ActualMarkedSlicedResponseRankOmega
public import Quartic.MarkedParentWitness

@[expose] public section

/-! The marked lower endpoint transfer in the finite middle range uses one
shared child: its exact marked flag, square certificate, and all closed
slices are chosen on the same preserved coefficient open. -/
noncomputable section
namespace Quartic.MarkedMiddleTransfer
open Module MvPolynomial UniformEndpoint RowMultiplicationCoordinates
open ActualDeformationColumnsOmega
variable {K : Type*} [Field K] [Infinite K] [IsAlgClosed K]
set_option maxHeartbeats 2000000

/-- A fixed admissible pure-pencil parameter gives the marked lower parent. -/
theorem lower_parent_witness_of_parameter (ω : K) (m : ℕ)
    (hmlo : 41 ≤ m) (hmhi : m ≤ 319)
    (hpositive : 0 < Counts.chi (m+3) (lowerEndpoint (m+3)))
    (hω : ω ≠ 0) (hω1 : ω ≠ -1) (hchild : MarkedEndpoints K m) :
    MarkedLowerWitness K (m+3) (lowerEndpoint (m+3)) := by
  classical
  have hm28 : 28 ≤ m := by omega
  have hcount : 4+(mixedCount m false+upperEndpoint m)=lowerEndpoint (m+3) := by
    have h := MarkedFiniteBounds.finite_lower_parent_count m hm28 hmhi
    omega
  have hpositive' : 0 < Counts.chi (m+3) (upperEndpoint m+mixedCount m false+4) := by
    rw [MarkedFiniteBounds.finite_lower_parent_count m hm28 hmhi]
    exact hpositive
  obtain ⟨hc,hbudget⟩ := MarkedEndpointBudget.block_budgets m hm28 false
  let ζ : MiddleCoordinates.Mixed K m := MarkedSquareEmbedding.zeta hc
  obtain ⟨A,hA,hAgood⟩ := MarkedSquareGenericOmega.genericMarkedAugmented_of_budget
    ω hω hω1 hc hbudget
  obtain ⟨g,r₀,E,hE,hg,hexp,D,hD,hgood⟩ :=
    MarkedExpansionCommonOpenOmega.exists_fixed_open_with (K := K) (L := K)
      ω m hmlo hmhi hpositive' hω hω1 A hA
  obtain ⟨B,hB,hflag⟩ := MarkedEndpointFlag.principal_open (K := K)
    (by omega : 1 ≤ m) (upperEndpoint m) rfl FixedBlockChildOpen.decode
    (isPolynomialFamily_linear FixedBlockChildOpen.decode)
    FixedBlockChildOpen.decode_surjective hchild
  have hDn : D ≠ 0 := by obtain ⟨a,ha⟩ := hD; intro hz; exact ha (by rw [hz,map_zero])
  have hBn : B ≠ 0 := by obtain ⟨a,ha⟩ := hB; intro hz; exact ha (by rw [hz,map_zero])
  have hDB : ∃ a, eval a (D*B) ≠ 0 :=
    PolynomialImageAvoidance.exists_eval_ne_zero (mul_ne_zero hDn hBn)
  obtain ⟨h,hhDB,Z,hZ⟩ := MarkedActualExpansionSlices.exists_ambient_slices_in_open
    m hm28 false g hg E hE hexp (D*B) hDB
  have hpair : eval (FixedBlockChildOpen.encodeChild h) D ≠ 0 ∧
      eval (FixedBlockChildOpen.encodeChild h) B ≠ 0 := by
    unfold FixedBlockChildOpen.encodeChild
    simpa only [map_mul,mul_ne_zero_iff] using hhDB
  obtain ⟨hblock,hf13,_,hApoint⟩ := hgood (FixedBlockChildOpen.encodeChild h) hpair.1
  have hdata := hflag (FixedBlockChildOpen.encodeChild h) hpair.2
  simp only [FixedBlockChildOpen.decode_encode] at hblock hf13 hApoint hdata
  obtain ⟨hh,hchildSurj,k,hk⟩ := hdata
  let U := (childMarkedCoefficient h k).range
  have hdim : (finrank K U : ℤ)=Counts.delta m (upperEndpoint m) := hk
  obtain ⟨Z',hclosed⟩ := MarkedExpansionMotionBridgeOmega.closed_slices
    hm28 g h U hdim Z hZ
  have hs := hblock.1.2.2.1
  rw [AugmentedGeneric.coefficientMixed_encode,AugmentedGeneric.coefficientChild_encode] at hs
  have htrace : Function.Injective
      (SplitMiddle31.mixedMultiplication (ActualTraceMotion.rowMixed g)) := by
    rw [ActualTraceMotion.rowMixed_eq_transpose]
    simpa only [AugmentedGeneric.coefficientMixed_encode,
      SimultaneousBlockConditionsOmega.transposeMixed,
      SimultaneousBlockConditions.transposeMixed] using hblock.2.2.1
  have ha := (hAgood (AugmentedGeneric.encode g h r₀) hApoint).2.2
  simp only [AugmentedGeneric.coefficientMixed_encode,
    AugmentedGeneric.coefficientMotions_encode] at ha
  rw [AugmentedGeneric.coefficientChild_encode] at ha
  have hr₀ : Function.Injective
      (ExtraCorrectionOmega.augmented ω g h r₀ (ExtraCorrectionOmega.squareClass h ζ)) := by
    rw [ExtraCorrectionOmega.augmented_square_eq]
    exact ha
  obtain ⟨r,s,_,hresponse⟩ := ActualMarkedSlicedResponseRankOmega.exists_response_rank_formula
    ω g h (ExtraCorrectionOmega.squareClass h ζ) U Z' hclosed
    hg hh hs htrace hf13.2.1 hf13.2.2 r₀ hr₀
  have hpos : 0 < Counts.chi (3+m) (4+(mixedCount m false+upperEndpoint m)) := by
    simpa only [Nat.add_comm 3 m,hcount] using hpositive
  have hw := MarkedParentWitness.of_response_formula ω g h s r k ζ U
    (canonical_marked_representatives h k) hg hh hs hchildSurj hf13.2.1 hf13.2.2
    hdim hpos hresponse
  simpa only [Nat.add_comm 3 m,hcount] using hw

/-- A marked exact child gives the marked lower endpoint throughout 41–319. -/
theorem lower_parent_witness (m : ℕ) (hmlo : 41 ≤ m) (hmhi : m ≤ 319)
    (hpositive : 0 < Counts.chi (m+3) (lowerEndpoint (m+3)))
    (hchild : MarkedEndpoints K m) :
    MarkedLowerWitness K (m+3) (lowerEndpoint (m+3)) := by
  obtain ⟨ω,hω,hω1⟩ := ThreeBlockOmega.exists_parameter (K := K)
  exact lower_parent_witness_of_parameter ω m hmlo hmhi hpositive hω hω1 hchild

end Quartic.MarkedMiddleTransfer
