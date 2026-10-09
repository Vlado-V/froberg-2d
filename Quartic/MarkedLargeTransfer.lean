module

public import Quartic.MarkedParentWitness
public import Quartic.MarkedEndpointFlag
public import Quartic.MarkedEndpointBudget
public import Quartic.StrongExpansionCommonOpenOmega
public import Quartic.StrongMarkedExpansionMotionBridgeOmega
public import Quartic.ActualMarkedSlicedResponseRankOmega
public import Quartic.SmallTransfer

@[expose] public section

/-! The marked lower transfer in the uniform large range. -/
noncomputable section
namespace Quartic.MarkedLargeTransfer
open Module MvPolynomial UniformEndpoint RowMultiplicationCoordinates
open ActualDeformationColumnsOmega
variable {K : Type*} [Field K] [Infinite K] [IsAlgClosed K]
set_option maxHeartbeats 2000000

theorem parent_witness (m : ℕ) (hm : 320 ≤ m)
    (hchild : MarkedEndpoints K m)
    (hpos : 0 < Counts.chi (m+3) (lowerEndpoint (m+3))) :
    MarkedLowerWitness K (m+3) (lowerEndpoint (m+3)) := by
  classical
  obtain ⟨ω,hω,hω1⟩ := ThreeBlockOmega.exists_parameter (K := K)
  obtain ⟨hc,hbudget⟩ := MarkedEndpointBudget.block_budgets m (by omega) false
  let ζ := MarkedSquareEmbedding.zeta (K := K) hc
  obtain ⟨A,hA,hAug⟩ := MarkedSquareGenericOmega.genericMarkedAugmented_of_budget
    ω hω hω1 hc hbudget
  obtain ⟨g,r₀,E,hE,hg,hexp,D,hD,hgood⟩ :=
    StrongExpansionCommonOpenOmega.exists_fixed_open_with (K := K) (L := K)
      ω m hm false hω hω1 A hA
  obtain ⟨B,hB,hflag⟩ := MarkedEndpointFlag.principal_open (by omega : 1 ≤ m)
    (upperEndpoint m) rfl FixedBlockChildOpen.decode
    (isPolynomialFamily_linear FixedBlockChildOpen.decode)
    FixedBlockChildOpen.decode_surjective hchild
  have hDn : D ≠ 0 := by obtain ⟨a,ha⟩ := hD; intro hz; exact ha (by rw [hz,map_zero])
  have hBn : B ≠ 0 := by obtain ⟨a,ha⟩ := hB; intro hz; exact ha (by rw [hz,map_zero])
  have hDB : ∃ a,eval a (D*B) ≠ 0 :=
    PolynomialImageAvoidance.exists_eval_ne_zero (mul_ne_zero hDn hBn)
  obtain ⟨h,hhDB,hslices⟩ := StrongActualSlices.exists_all_corrections_in_open
    (I := Fin ((m+1).choose 2+2)) m hm false
    (fun w => StrongActualSlices.markedCorrectionCount m false w.val)
    g hg E hE hexp (D*B) hDB
  have hp : eval (FixedBlockChildOpen.encodeChild h) D ≠ 0 ∧
      eval (FixedBlockChildOpen.encodeChild h) B ≠ 0 := by
    simpa only [map_mul,mul_ne_zero_iff] using hhDB
  obtain ⟨hblock,hf13,_,hApoint⟩ := hgood _ hp.1
  have hdata := hflag _ hp.2
  simp only [FixedBlockChildOpen.decode_encode] at hblock hf13 hApoint hdata
  obtain ⟨hh,hsurj,k,hk⟩ := hdata
  let U := (childMarkedCoefficient h k).range
  have hdim : (finrank K U:ℤ)=Counts.delta m (upperEndpoint m) := hk
  have hUle : finrank K U ≤ (m+1).choose 2 := by
    calc
      finrank K U ≤ finrank K (Forms K m 2 ⧸ Submodule.span K (Set.range h)) :=
        Submodule.finrank_le U
      _ ≤ finrank K (Forms K m 2) := Submodule.finrank_quotient_le _
      _ = (m+1).choose 2 := finrank_quadrics K m
  let w : Fin ((m+1).choose 2+2) := ⟨finrank K U+1,by omega⟩
  obtain ⟨Z,hclosed⟩ := StrongMarkedExpansionMotionBridgeOmega.closed_slices hm g h U (hslices w)
  have hs := hblock.1.2.2.1
  rw [AugmentedGeneric.coefficientMixed_encode,AugmentedGeneric.coefficientChild_encode] at hs
  have htrace : Function.Injective (SplitMiddle31.mixedMultiplication (ActualTraceMotion.rowMixed g)) := by
    rw [ActualTraceMotion.rowMixed_eq_transpose]
    simpa only [AugmentedGeneric.coefficientMixed_encode,
      SimultaneousBlockConditionsOmega.transposeMixed,
      SimultaneousBlockConditions.transposeMixed] using hblock.2.2.1
  have haug := (hAug _ hApoint).2.2
  simp only [AugmentedGeneric.coefficientMixed_encode,AugmentedGeneric.coefficientChild_encode,
    AugmentedGeneric.coefficientMotions_encode] at haug
  rw [AugmentedGeneric.coefficientChild_encode] at haug
  have haug' : Function.Injective (ExtraCorrectionOmega.augmented ω g h r₀
      (ExtraCorrectionOmega.squareClass h ζ)) := by
    rw [ExtraCorrectionOmega.augmented_square_eq]
    exact haug
  obtain ⟨r,s,_,hrank⟩ := ActualMarkedSlicedResponseRankOmega.exists_response_rank_formula
    ω g h (ExtraCorrectionOmega.squareClass h ζ) U Z hclosed hg hh hs htrace
    hf13.2.1 hf13.2.2 r₀ haug'
  have hpos' : 0 < Counts.chi (3+m) (4+(mixedCount m false+upperEndpoint m)) := by
    simpa only [SmallTransfer.parent_count m (by omega) false,parentCount,
      Bool.false_eq_true,ite_false,Nat.add_comm 3 m] using hpos
  have hw := MarkedParentWitness.of_response_formula ω g h s r k ζ U
    (canonical_marked_representatives h k) hg hh hs hsurj hf13.2.1 hf13.2.2 hdim hpos' hrank
  simpa only [SmallTransfer.parent_count m (by omega) false,parentCount,
    Bool.false_eq_true,ite_false,Nat.add_comm 3 m] using hw

end Quartic.MarkedLargeTransfer
