module

public import Quartic.SplitDefectCokernel
public import Quartic.TransferRankCount

@[expose] public section

/-! The two defect inequalities from the actual split and response ranks.
No child endpoint exactness is assumed. -/
noncomputable section
namespace Quartic.DefectRankCount
open Module ActualSplitCokernel SplitDefectCokernel
variable {K : Type*} [Field K] {m c q : ℕ}

/-- The split rank loses precisely at most the outer cokernel and the child cokernel. -/
theorem split_rank_lower (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2)
    (h22 : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (hh : LinearIndependent K h)
    (hcubic : Function.Injective (CubicGeneric.cubicMap h))
    (h13 : Function.Injective (GeneralF13.f13Map g h)) :
    Counts.b4 (3+m) - Counts.j m q c -
      (finrank K (QuarticQuotient K m
        (Submodule.span K (Set.range (fun i => (h i).val)))) : ℤ) ≤
      finrank K (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range := by
  have hb := cokernel_finrank_le g h h22
  have hs := (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range.finrank_quotient_add_finrank
  have hchild := (quadraticMultiplication h).range.finrank_quotient_add_finrank
  have hc := quartic_quotient_add_rank h
  have hj := rawJ_finrank_eq_j g h hh hcubic h13
  rw [finrank_quartics] at hs hchild
  change finrank K (Cokernel g h) + _ = _ at hs
  change finrank K (ChildCokernel h) + _ = _ at hchild
  unfold Counts.b4
  omega

/-- Both actual parent defects are bounded by the same two child defects. -/
theorem defect_bounds_of_gain (f : Fin (4+(c+q)) → Forms K (3+m) 2)
    (hf : LinearIndependent K f) (split response c₀ k₀ : ℕ)
    (hsplit : Counts.b4 (3+m)-Counts.j m q c-c₀ ≤ (split : ℤ))
    (hresponse : min (Counts.hTotal m q c+c₀-k₀) (Counts.j m q c) ≤ (response : ℤ))
    (hgain : split+response ≤ finrank K (quadraticMultiplication f).range) :
    (finrank K (QuarticHomology f) : ℤ) ≤
        max (k₀ : ℤ) ((c₀ : ℤ)-Counts.chi (3+m) (4+(c+q))) ∧
    (finrank K (QuarticQuotient K (3+m)
        (Submodule.span K (Set.range (fun i => (f i).val)))) : ℤ) ≤
        max (c₀ : ℤ) ((k₀ : ℤ)+Counts.chi (3+m) (4+(c+q))) := by
  have hsum := quartic_quotient_add_rank f
  have heuler := quartic_euler_identity f hf
  have htransfer := Counts.transfer_euler_identity m q c
  have hn : m+3=3+m := by omega
  have hr : q+c+4=4+(c+q) := by omega
  rw [hn,hr] at htransfer
  unfold Counts.b4 at hsplit
  omega

end Quartic.DefectRankCount
