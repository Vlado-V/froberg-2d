import Froberg.ProjectedSparseCapacity
import Froberg.PreparedActualCapacities

/-! Every active higher row meets the projected private-output capacity;
zero-count inactive rows use zero sparse blocks. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
variable {K : Type} [Field K] [Infinite K]

theorem paired_output_finrank (w R : ℕ) :
    finrank K (homogeneousSubmodule (Fin w × Bool) K R)=(2*w+R-1).choose R := by
  rw [Module.finrank_eq_card_basis (finiteVariableFormsBasis (Fin w × Bool) R),Sym.card_sym_eq_choose]
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  congr 2
  omega

theorem eventually_all_private_projected_capacity {d : ℕ} (hd : 3≤d) :
    ∀ᶠ w : ℕ in atTop,∀ R : allEvenIndices d,R.val≠2 →
      (if R.val∈activeEvenIndices d then
        sparseBlockCount ((101/100 : ℝ)*higherCountGamma d R.val) R.val (d-R.val) w else 0)*
          (d-R.val+1).choose (d-R.val)≤oddOutputDimension w R.val-
            finrank K (homogeneousSubmodule (Fin w × Bool) K (R.val-1)) := by
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
    simpa only [if_pos ha,paired_output_finrank] using hw
  · exact Eventually.of_forall fun _ _ => by simp only [if_neg ha,zero_mul,Nat.zero_le]

end Froberg.PreparedParameters
