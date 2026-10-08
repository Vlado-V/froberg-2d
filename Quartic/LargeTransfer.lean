import Quartic.FixedBlockChildOpen
import Quartic.ExpansionMotionBridge
import Quartic.ActualSlicedResponseRank
import Quartic.SmallTransfer

/-! Uniform actual three-variable transfer for every child dimension at least 41. -/
noncomputable section
namespace Quartic.LargeTransfer
open Module UniformEndpoint ActualDeformationColumns ActualDeformationResponse
open RowMultiplicationCoordinates
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
set_option maxHeartbeats 1500000

theorem parent_witness (m : ℕ) (hm : 41 ≤ m) (upper : Bool)
    (hchild : ∀ q,q ≤ (m+1).choose 2 → GenericQuartic K m q) :
    QuarticWitness K (m+3) (parentCount m upper) := by
  classical
  obtain ⟨g,r₀,E,hE,hg,hexp,D,hD,hgood⟩ := FixedBlockChildOpen.exists_fixed_open (K := K) m hm upper hchild
  obtain ⟨h,hhD,Z,hZ⟩ := ActualExpansionSlices.exists_ambient_slices_in_open m (by omega) upper
    g hg E hE hexp D hD
  obtain ⟨hblock,hf13,_,hflag⟩ := hgood (FixedBlockChildOpen.encodeChild h) hhD
  simp only [FixedBlockChildOpen.decode_encode] at hblock hf13 hflag
  obtain ⟨hh,hchildSurj,k,hk⟩ := hflag
  let U := (childMarkedCoefficient h k).range
  have hdim : (finrank K U:ℤ)=Counts.delta m (upperEndpoint m) := hk
  obtain ⟨Z',hclosed⟩ := ExpansionMotionBridge.closed_slices (by omega : 28 ≤ m) g h U hdim Z hZ
  have hmixedEncode := AugmentedGeneric.coefficientMixed_encode g h r₀
  have hchildEncode := AugmentedGeneric.coefficientChild_encode g h r₀
  have hmotionsEncode := AugmentedGeneric.coefficientMotions_encode g h r₀
  have hs := hblock.1.2.2.1
  have hr₀ := hblock.1.2.2.2
  rw [hmixedEncode] at hs hr₀
  rw [hchildEncode] at hs hr₀
  rw [hmotionsEncode] at hr₀
  have htrace : Function.Injective (SplitMiddle31.mixedMultiplication (ActualTraceMotion.rowMixed g)) := by
    simpa only [AugmentedGeneric.coefficientMixed_encode] using
      ActualTraceMotion.mixedMultiplication_injective_of_blockConditions (AugmentedGeneric.encode g h r₀) hblock
  obtain ⟨r,s,_,hresponse⟩ := ActualSlicedResponseRank.exists_response_rank_formula g h U Z' hclosed
    hg hh hs htrace hf13.2.1 hf13.2.2 r₀ hr₀
  have hresponse' : (finrank K (response g h r U s).range:ℤ)=
      min (Counts.hTotal m (upperEndpoint m) (mixedCount m upper))
        (Counts.j m (upperEndpoint m) (mixedCount m upper)) := by
    rw [hresponse,hdim]
    congr 1
    unfold Counts.hTotal Counts.k31
    push_cast
    ring
  obtain ⟨ε,_,hlin,hgain⟩ := ActualDeformationRank.exists_independent_rank_gain
    g h s r k U (canonical_marked_representatives h k) hg hh
  let f := deformedFamily g h s r (Pi.single k markedDirection) ε
  have hsplit := ActualSplitCokernel.split_rank_eq g h hs hchildSurj hh hf13.2.1 hf13.2.2
  have hdimParent := TransferRankCount.expected_of_gain f hlin _ _ hsplit hresponse' hgain
  have hw := EndpointReduction.witness_of_ordered f hlin hdimParent
  simpa only [SmallTransfer.parent_count m (by omega) upper,Nat.add_comm 3 m] using hw

/-- The full generic statement transfers for every m≥41 and every admissible
parent generator count, with no large-range cutoff. -/
theorem transfer (m : ℕ) (hm : 41 ≤ m)
    (hchild : ∀ q,q ≤ (m+1).choose 2 → GenericQuartic K m q) :
    ∀ r,r ≤ (m+3+1).choose 2 → GenericQuartic K (m+3) r := by
  intro r hr
  have hl := parent_witness m hm false hchild
  have hh := parent_witness m hm true hchild
  simp only [parentCount,Bool.false_eq_true,ite_false,ite_true] at hl hh
  apply EndpointReduction.adjacent_endpoints_imply_generic (lowerEndpoint (m+3)) (upperEndpoint (m+3))
    (lower_upper_adjacent (m+3)).2 hl hh _ (upper_nonpositive (m+3)) hr
  unfold lowerEndpoint
  split_ifs with hz
  · omega
  · have hpos := SharedChildFlag.upper_positive (by omega : 1 ≤ m+3)
    exact (before_upper_positive (m+3) (upperEndpoint (m+3)-1) (by omega)).le

end Quartic.LargeTransfer
