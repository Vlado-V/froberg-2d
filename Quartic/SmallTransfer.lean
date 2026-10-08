import Quartic.SmallTransferData
import Quartic.ActualDeformationRank
import Quartic.TransferRankCount

/-! The actual three-variable transfer for child dimensions 28 through 40. -/
noncomputable section
namespace Quartic.SmallTransfer
open Module UniformEndpoint ActualSmallMotionAvoidance ActualDeformationColumns
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
set_option maxHeartbeats 1500000

theorem parent_count (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    4+(mixedCount m upper+upperEndpoint m)=parentCount m upper := by
  have hc := (EndpointBlockConditions.structural_counts m hm upper).1
  unfold mixedCount at hc ⊢
  omega

/-- At either actual parent endpoint the shared child data and exact deformation
produce an independent quadratic family with the asserted quartic dimension. -/
theorem parent_witness (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40) (upper : Bool)
    (hchild : ∀ q,q ≤ (m+1).choose 2 → GenericQuartic K m q) :
    QuarticWitness K (m+3) (parentCount m upper) := by
  obtain ⟨p,k,r,s,hblock,hf13,hchildSurj,_,_,hresponse⟩ :=
    SmallTransferData.exists_data (K := K) m hmlo hmhi upper hchild
  let U := (childMarkedCoefficient (Q p) k).range
  obtain ⟨ε,_,hlin,hgain⟩ := ActualDeformationRank.exists_independent_rank_gain
    (G p) (Q p) s r k U (canonical_marked_representatives (Q p) k) hblock.1.1 hblock.1.2.1
  let f := deformedFamily (G p) (Q p) s r (Pi.single k markedDirection) ε
  have hdim : finrank K (QuarticQuotient K (3+m)
      (Submodule.span K (Set.range (fun i => (f i).val))))=
        expectedDimension (3+m) (4+(mixedCount m upper+upperEndpoint m)) := by
    have hsplit := ActualSplitCokernel.split_rank_eq (G p) (Q p) hblock.1.2.2.1 hchildSurj
      hf13.1 hf13.2.1 hf13.2.2
    exact TransferRankCount.expected_of_gain f hlin _ _ hsplit hresponse hgain
  have hw := EndpointReduction.witness_of_ordered f hlin hdim
  simpa only [parent_count m hmlo upper,Nat.add_comm 3 m] using hw

/-- This is a genuine transfer of the complete actual generic statement,
with the child premise explicit and all parent generator counts covered. -/
theorem transfer (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40)
    (hchild : ∀ q,q ≤ (m+1).choose 2 → GenericQuartic K m q) :
    ∀ r,r ≤ (m+3+1).choose 2 → GenericQuartic K (m+3) r := by
  intro r hr
  have hl := parent_witness m hmlo hmhi false hchild
  have hh := parent_witness m hmlo hmhi true hchild
  simp only [parentCount,Bool.false_eq_true,ite_false,ite_true] at hl hh
  apply EndpointReduction.adjacent_endpoints_imply_generic (lowerEndpoint (m+3)) (upperEndpoint (m+3))
    (lower_upper_adjacent (m+3)).2 hl hh _ (upper_nonpositive (m+3)) hr
  unfold lowerEndpoint
  split_ifs with hz
  · omega
  · have hpos := SharedChildFlag.upper_positive (by omega : 1 ≤ m+3)
    exact (before_upper_positive (m+3) (upperEndpoint (m+3)-1) (by omega)).le

end Quartic.SmallTransfer
