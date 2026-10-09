module

public import Froberg.PreparedPrivateProjectedCapacity

@[expose] public section

noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter

theorem eventually_field_uniform_private_projected_capacity {d : ℕ} (hd : 3≤d) :
    ∀ᶠ w : ℕ in atTop,∀ (K : Type) [Field K] [Infinite K],∀ R : allEvenIndices d,R.val≠2 →
      (if R.val∈activeEvenIndices d then
        sparseBlockCount ((101/100 : ℝ)*higherCountGamma d R.val) R.val (d-R.val) w else 0)*
          (d-R.val+1).choose (d-R.val)≤oddOutputDimension w R.val-
            finrank K (homogeneousSubmodule (Fin w × Bool) K (R.val-1)) := by
  have hall : ∀ᶠ w : ℕ in atTop,∀ R : allEvenIndices d,R.val≠2 →
      (if R.val∈activeEvenIndices d then
        sparseBlockCount ((101/100 : ℝ)*higherCountGamma d R.val) R.val (d-R.val) w else 0)*
          (d-R.val+1).choose (d-R.val)≤oddOutputDimension w R.val-
            (2*w+(R.val-1)-1).choose (R.val-1) := by
    apply eventually_all.mpr
    intro R
    by_cases hR2 : R.val=2
    · exact Eventually.of_forall fun _ h => False.elim (h hR2)
    by_cases ha : R.val∈activeEvenIndices d
    · have hR : R.val∈activeHigherIndices d := by
        apply Finset.mem_filter.mpr
        refine ⟨ha,?_⟩
        have hm := mem_allEvenIndices.mp R.property
        omega
      filter_upwards [eventually_higher_sparse_projected_capacity hd hR] with w hw _
      simpa only [if_pos ha] using hw
    · exact Eventually.of_forall fun _ _ => by simp only [if_neg ha,zero_mul,Nat.zero_le]
  filter_upwards [hall] with w hw
  intro K _ _ R hR
  simpa only [paired_output_finrank] using hw R hR

end Froberg.PreparedParameters
