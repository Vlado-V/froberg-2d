module

public import Froberg.QuadraticMarkedFlag
public import Quartic.StrongExpansionCommonOpen
public import Quartic.StrongExpansionMotionBridge
public import Quartic.ActualSlicedResponseRank
public import Quartic.ActualDeformationRank
public import Quartic.DefectRankCount

@[expose] public section

/-! The three-variable quadratic transfer retains arbitrary child defects. -/
noncomputable section
namespace Froberg.QuadraticNonTwoTransfer
open Module MvPolynomial Quartic UniformEndpoint
open ActualDeformationColumns ActualDeformationResponse RowMultiplicationCoordinates
variable {K : Type*} [Field K] [Infinite K] [IsAlgClosed K]
set_option maxHeartbeats 2000000

theorem parent_defect_witness (m : ℕ) (hm : 320 ≤ m) (upper : Bool)
    (h2 : (2 : K) ≠ 0) :
    ∃ f : Fin (4+(mixedCount m upper+upperEndpoint m)) → Forms K (3+m) 2,
      LinearIndependent K f ∧
      (finrank K (QuarticHomology f) : ℤ) ≤ max (genericHomology K m 2 (upperEndpoint m-1) : ℤ)
          ((genericCokernel K m 2 (upperEndpoint m) : ℤ)-
            Counts.chi (3+m) (4+(mixedCount m upper+upperEndpoint m))) ∧
      (finrank K (QuadraticChildFlag.Coker f) : ℤ) ≤ max (genericCokernel K m 2 (upperEndpoint m) : ℤ)
          ((genericHomology K m 2 (upperEndpoint m-1) : ℤ)+
            Counts.chi (3+m) (4+(mixedCount m upper+upperEndpoint m))) := by
  classical
  obtain ⟨g,r₀,E,hE,hg,hexp,D,hD,hgood⟩ :=
    StrongExpansionCommonOpen.exists_fixed_open (K := K) (L := K) m hm upper h2
  obtain ⟨A,hA,hflag⟩ := QuadraticMarkedFlag.principal_open (K := K) (by omega : 0 < m) h2
  obtain ⟨a,haD,haA⟩ := principal_opens_intersect hD hA
  have hDA : ∃ a,eval a (D*A) ≠ 0 := ⟨a,by simpa only [map_mul] using mul_ne_zero haD haA⟩
  obtain ⟨h,hhDA,hslices⟩ := StrongActualSlices.exists_all_corrections_in_open
    (I := Fin ((m+1).choose 2+1)) m hm upper
    (fun w => StrongActualSlices.markedCorrectionCount m upper w.val)
    g hg E hE hexp (D*A) hDA
  have hpair : eval (FixedBlockChildOpen.encodeChild h) D ≠ 0 ∧
      eval (FixedBlockChildOpen.encodeChild h) A ≠ 0 := by
    simpa only [map_mul,mul_ne_zero_iff] using hhDA
  obtain ⟨hblock,hf13,_⟩ := hgood _ hpair.1
  have hdata := hflag _ hpair.2
  simp only [FixedBlockChildOpen.decode_encode] at hblock hf13 hdata
  obtain ⟨hh,hc,k,hk⟩ := hdata
  let U := (childMarkedCoefficient h k).range
  have hdim : (finrank K U : ℤ)=Counts.delta m (upperEndpoint m)+
      genericCokernel K m 2 (upperEndpoint m)-genericHomology K m 2 (upperEndpoint m-1) := hk
  have hUle : finrank K U ≤ (m+1).choose 2 := by
    calc
      finrank K U ≤ finrank K (Forms K m 2 ⧸ Submodule.span K (Set.range h)) :=
        Submodule.finrank_le U
      _ ≤ finrank K (Forms K m 2) := Submodule.finrank_quotient_le _
      _ = (m+1).choose 2 := finrank_quadrics K m
  let w : Fin ((m+1).choose 2+1) := ⟨finrank K U,by omega⟩
  obtain ⟨Z,hclosed⟩ := StrongExpansionMotionBridge.closed_slices hm g h U (hslices w)
  have hs := hblock.1.2.2.1
  have hr₀ := hblock.1.2.2.2
  rw [AugmentedGeneric.coefficientMixed_encode,AugmentedGeneric.coefficientChild_encode] at hs hr₀
  rw [AugmentedGeneric.coefficientMotions_encode] at hr₀
  have htrace : Function.Injective (SplitMiddle31.mixedMultiplication (ActualTraceMotion.rowMixed g)) := by
    simpa only [AugmentedGeneric.coefficientMixed_encode] using
      ActualTraceMotion.mixedMultiplication_injective_of_blockConditions
        (AugmentedGeneric.encode g h r₀) hblock
  obtain ⟨r,s,_,hresponse⟩ := ActualSlicedResponseRank.exists_response_rank_formula g h U Z hclosed
    hg hh hs htrace hf13.2.1 hf13.2.2 r₀ hr₀
  have hresponse' : (finrank K (response g h r U s).range : ℤ)=
      min (Counts.hTotal m (upperEndpoint m) (mixedCount m upper)+
        genericCokernel K m 2 (upperEndpoint m)-genericHomology K m 2 (upperEndpoint m-1))
        (Counts.j m (upperEndpoint m) (mixedCount m upper)) := by
    rw [hresponse,hdim]
    congr 1
    unfold Counts.hTotal Counts.k31
    push_cast
    ring
  obtain ⟨ε,_,hlin,hgain⟩ := ActualDeformationRank.exists_independent_rank_gain
    g h s r k U (canonical_marked_representatives h k) hg hh
  let f := deformedFamily g h s r (Pi.single k markedDirection) ε
  have hsplit := DefectRankCount.split_rank_lower g h hs hh hf13.2.1 hf13.2.2
  rw [hc] at hsplit
  refine ⟨f,hlin,?_⟩
  exact DefectRankCount.defect_bounds_of_gain f hlin _ _
    (genericCokernel K m 2 (upperEndpoint m)) (genericHomology K m 2 (upperEndpoint m-1))
    hsplit hresponse'.ge hgain

end Froberg.QuadraticNonTwoTransfer
