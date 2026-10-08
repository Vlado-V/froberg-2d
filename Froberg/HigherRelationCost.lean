import Froberg.ScalarSeparationAsymptotic

/-! The exact number of C.13 coefficient equations is lower order than
the graph and scalar-shadow scales used in C.4. -/
noncomputable section
namespace Froberg
open Filter Finset
open scoped Topology

def higherRelationCost (d h u m : ℕ) : ℕ :=
  u*∑ r : Fin ((d-1)/2),
    (h+2*(r.val+1)-1).choose (2*(r.val+1))*
      (m+(d-2*(r.val+1))-1).choose (d-2*(r.val+1))

theorem higherRelationCost_lower_order {d : ℕ} (hd : 3≤d) (h u : ℕ) :
    Tendsto (fun m : ℕ => (higherRelationCost d h u m : ℝ)/(m : ℝ)^(d-1))
      atTop (𝓝 0) := by
  have hi (r : Fin ((d-1)/2)) :=
    (monomial_count_normalized_small_tendsto
      (show d-2*(r.val+1)<d-1 by omega)).const_mul
        (((h+2*(r.val+1)-1).choose (2*(r.val+1)) : ℕ) : ℝ)
  have hs := (tendsto_finsetSum univ (fun r _ => hi r)).const_mul (u : ℝ)
  simpa only [higherRelationCost,Nat.cast_mul,Nat.cast_sum,mul_zero,sum_const_zero,
    ←mul_div_assoc,←sum_div] using hs

theorem higherRelationCost_shadow_lower_order {d : ℕ} (hd : 3≤d) (h u : ℕ) :
    Tendsto (fun m : ℕ => (higherRelationCost d h u m : ℝ)/(m : ℝ)^d)
      atTop (𝓝 0) := by
  have hi (r : Fin ((d-1)/2)) :=
    (monomial_count_normalized_small_tendsto
      (show d-2*(r.val+1)<d by omega)).const_mul
        (((h+2*(r.val+1)-1).choose (2*(r.val+1)) : ℕ) : ℝ)
  have hs := (tendsto_finsetSum univ (fun r _ => hi r)).const_mul (u : ℝ)
  simpa only [higherRelationCost,Nat.cast_mul,Nat.cast_sum,mul_zero,sum_const_zero,
    ←mul_div_assoc,←sum_div] using hs

end Froberg
