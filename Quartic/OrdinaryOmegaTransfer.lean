module

public import Quartic.OrdinaryOmegaTransferData
public import Quartic.FixedBlockChildOpenOmega
public import Quartic.ExpansionMotionBridgeOmega
public import Quartic.ActualSlicedResponseRankOmega
public import Quartic.ActualDeformationRankOmega
public import Quartic.TransferRankCount

@[expose] public section

/-! Ordinary endpoint transfer using the modified pure pencil and a marked
child endpoint property. This theorem does not yet retain a parent square. -/
noncomputable section
namespace Quartic.OrdinaryOmegaTransfer
open Module UniformEndpoint ActualSmallMotionAvoidanceOmega
open ActualDeformationColumnsOmega ActualDeformationResponseOmega RowMultiplicationCoordinates
variable {K : Type*} [Field K] [IsAlgClosed K]
variable (ω : K)
set_option maxHeartbeats 1500000

theorem parent_count (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    4+(mixedCount m upper+upperEndpoint m)=parentCount m upper := by
  have hc := (EndpointBlockConditions.structural_counts m hm upper).1
  unfold mixedCount at hc ⊢
  omega

/-- At either actual parent endpoint the shared child data and exact deformation
produce an independent quadratic family with the asserted quartic dimension. -/
theorem small_parent_witness (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40) (upper : Bool) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (hchild : MarkedEndpoints K m) :
    QuarticWitness K (m+3) (parentCount m upper) := by
  obtain ⟨p,k,r,s,hblock,hf13,hchildSurj,_,_,hresponse⟩ :=
    OrdinaryOmegaTransferData.exists_data (K := K) ω m hmlo hmhi upper hω hω1 hchild
  let U := (childMarkedCoefficient (Q p) k).range
  obtain ⟨ε,_,hlin,hgain⟩ := ActualDeformationRankOmega.exists_independent_rank_gain ω
    (G p) (Q p) s r k U (canonical_marked_representatives (Q p) k) hblock.1.1 hblock.1.2.1
  let f := deformedFamily (G p) (Q p) s r (Pi.single k (markedDirection ω)) ε
  have hdim : finrank K (QuarticQuotient K (3+m)
      (Submodule.span K (Set.range (fun i => (f i).val))))=
        expectedDimension (3+m) (4+(mixedCount m upper+upperEndpoint m)) := by
    have hsplit := ActualSplitCokernel.split_rank_eq (G p) (Q p) hblock.1.2.2.1 hchildSurj
      hf13.1 hf13.2.1 hf13.2.2
    exact TransferRankCount.expected_of_gain f hlin _ _ hsplit hresponse hgain
  have hw := EndpointReduction.witness_of_ordered f hlin hdim
  simpa only [parent_count m hmlo upper,Nat.add_comm 3 m] using hw

theorem large_parent_witness (m : ℕ) (hm : 41 ≤ m) (upper : Bool) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (hchild : MarkedEndpoints K m) :
    QuarticWitness K (m+3) (parentCount m upper) := by
  classical
  obtain ⟨g,r₀,E,hE,hg,hexp,D,hD,hgood⟩ := FixedBlockChildOpenOmega.exists_fixed_open (K := K) ω m hm upper hω hω1 hchild
  obtain ⟨h,hhD,Z,hZ⟩ := ActualExpansionSlices.exists_ambient_slices_in_open m (by omega) upper
    g hg E hE hexp D hD
  obtain ⟨hblock,hf13,_,hflag⟩ := hgood (FixedBlockChildOpen.encodeChild h) hhD
  simp only [FixedBlockChildOpen.decode_encode] at hblock hf13 hflag
  obtain ⟨hh,hchildSurj,k,hk⟩ := hflag
  let U := (childMarkedCoefficient h k).range
  have hdim : (finrank K U:ℤ)=Counts.delta m (upperEndpoint m) := hk
  obtain ⟨Z',hclosed⟩ := ExpansionMotionBridgeOmega.closed_slices (by omega : 28 ≤ m) g h U hdim Z hZ
  have hmixedEncode := AugmentedGeneric.coefficientMixed_encode g h r₀
  have hchildEncode := AugmentedGeneric.coefficientChild_encode g h r₀
  have hmotionsEncode := AugmentedGeneric.coefficientMotions_encode g h r₀
  have hs := hblock.1.2.2.1
  have hr₀ := hblock.1.2.2.2
  rw [hmixedEncode] at hs hr₀
  rw [hchildEncode] at hs hr₀
  rw [hmotionsEncode] at hr₀
  have htrace : Function.Injective (SplitMiddle31.mixedMultiplication (ActualTraceMotion.rowMixed g)) := by
    rw [ActualTraceMotion.rowMixed_eq_transpose]
    simpa only [AugmentedGeneric.coefficientMixed_encode,
      SimultaneousBlockConditionsOmega.transposeMixed,
      SimultaneousBlockConditions.transposeMixed] using hblock.2.2.1
  obtain ⟨r,s,_,hresponse⟩ := ActualSlicedResponseRankOmega.exists_response_rank_formula ω g h U Z' hclosed
    hg hh hs htrace hf13.2.1 hf13.2.2 r₀ hr₀
  have hresponse' : (finrank K (response ω g h r U s).range:ℤ)=
      min (Counts.hTotal m (upperEndpoint m) (mixedCount m upper))
        (Counts.j m (upperEndpoint m) (mixedCount m upper)) := by
    rw [hresponse,hdim]
    congr 1
    unfold Counts.hTotal Counts.k31
    push_cast
    ring
  obtain ⟨ε,_,hlin,hgain⟩ := ActualDeformationRankOmega.exists_independent_rank_gain ω
    g h s r k U (canonical_marked_representatives h k) hg hh
  let f := deformedFamily g h s r (Pi.single k (markedDirection ω)) ε
  have hsplit := ActualSplitCokernel.split_rank_eq g h hs hchildSurj hh hf13.2.1 hf13.2.2
  have hdimParent := TransferRankCount.expected_of_gain f hlin _ _ hsplit hresponse' hgain
  have hw := EndpointReduction.witness_of_ordered f hlin hdimParent
  simpa only [parent_count m (by omega) upper,Nat.add_comm 3 m] using hw

/-- Both ordinary parent endpoints follow from a marked exact child. -/
theorem parent_witness (m : ℕ) (hm : 28 ≤ m) (upper : Bool)
    (hω : ω ≠ 0) (hω1 : ω ≠ -1) (hchild : MarkedEndpoints K m) :
    QuarticWitness K (m + 3) (parentCount m upper) := by
  by_cases hsmall : m ≤ 40
  · exact small_parent_witness ω m hm hsmall upper hω hω1 hchild
  · exact large_parent_witness ω m (by omega) upper hω hω1 hchild

/-- Generic maximal rank at every parent count. -/
theorem transfer (m : ℕ) (hm : 28 ≤ m) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (hchild : MarkedEndpoints K m) :
    ∀ r, r ≤ (m + 3 + 1).choose 2 → GenericQuartic K (m + 3) r := by
  intro r hr
  have hl := parent_witness ω m hm false hω hω1 hchild
  have hh := parent_witness ω m hm true hω hω1 hchild
  simp only [parentCount, Bool.false_eq_true, ite_false, ite_true] at hl hh
  apply EndpointReduction.adjacent_endpoints_imply_generic
    (lowerEndpoint (m + 3)) (upperEndpoint (m + 3))
    (lower_upper_adjacent (m + 3)).2 hl hh _ (upper_nonpositive (m + 3)) hr
  unfold lowerEndpoint
  split_ifs with hz
  · omega
  · have hp := SharedChildFlag.upper_positive (by omega : 1 ≤ m + 3)
    exact (before_upper_positive (m + 3) (upperEndpoint (m + 3) - 1) (by omega)).le

/-- The admissible pencil parameter is chosen internally. -/
theorem ordinary_parent_witness (m : ℕ) (hm : 28 ≤ m) (upper : Bool)
    (hchild : MarkedEndpoints K m) :
    QuarticWitness K (m + 3) (parentCount m upper) := by
  obtain ⟨ω, hω, hω1⟩ := ThreeBlockOmega.exists_parameter (K := K)
  exact parent_witness ω m hm upper hω hω1 hchild

/-- A marked child supplies ordinary generic maximal rank at every parent
count, with no pencil parameter left as a premise. -/
theorem ordinary_transfer (m : ℕ) (hm : 28 ≤ m) (hchild : MarkedEndpoints K m) :
    ∀ r, r ≤ (m + 3 + 1).choose 2 → GenericQuartic K (m + 3) r := by
  obtain ⟨ω, hω, hω1⟩ := ThreeBlockOmega.exists_parameter (K := K)
  exact transfer ω m hm hω hω1 hchild

end Quartic.OrdinaryOmegaTransfer
