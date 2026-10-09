module

public import Froberg.ScalarSeparationAsymptotic
public import Froberg.OddBiformDecomposition

@[expose] public section

/-! Every odd coefficient layer has positive X-degree, so its total
Y-dimension is lower order than the scalar degree-d count. -/
noncomputable section
namespace Froberg
open Filter Finset Module
open scoped Topology

def oddCoefficientCount (d h m : ℕ) : ℕ :=
  ∑ r : Fin ((d+1)/2), (h+(2*r.val+1)-1).choose (2*r.val+1)*
    (m+(d-(2*r.val+1))-1).choose (d-(2*r.val+1))

theorem oddCoefficientCount_lower_order {d : ℕ} (hd : 0<d) (h : ℕ) :
    Tendsto (fun m : ℕ => (oddCoefficientCount d h m : ℝ)/(m : ℝ)^d)
      atTop (𝓝 0) := by
  have hi (r : Fin ((d+1)/2)) :=
    (monomial_count_normalized_small_tendsto
      (show d-(2*r.val+1)<d by omega)).const_mul
        (((h+(2*r.val+1)-1).choose (2*r.val+1) : ℕ) : ℝ)
  have hs := tendsto_finsetSum univ (fun r _ => hi r)
  simpa only [oddCoefficientCount,Nat.cast_mul,Nat.cast_sum,mul_zero,sum_const_zero,
    ←mul_div_assoc,←sum_div] using hs

theorem bounded_oddCoefficientCount_lower_order {d : ℕ} (hd : 0<d) (h : ℕ)
    (a : ℕ → ℕ) (ha : ∀ᶠ m : ℕ in atTop,a m≤oddCoefficientCount d h m) :
    Tendsto (fun m : ℕ => (a m : ℝ)/(m : ℝ)^d) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) _
    (oddCoefficientCount_lower_order hd h)
  exact ha.mono fun m hm => div_le_div_of_nonneg_right (by exact_mod_cast hm) (by positivity)

theorem odd_biform_finrank_lower_order (K : Type) [Field K] [Infinite K]
    {d h : ℕ} (hd : 0<d) (hh : 0<h) :
    Tendsto (fun m : ℕ => (finrank K (biformParitySpace K h m d 1) : ℝ)/(m : ℝ)^d)
      atTop (𝓝 0) := by
  apply (oddCoefficientCount_lower_order hd h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  rw [finrank_odd_biform_space hh hm]
  rfl

end Froberg
