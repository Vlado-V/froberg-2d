import Froberg.PreparedLayeredBudget
import Froberg.OddBackgroundSource

/-! The actual old odd coefficient quotient has at most the full odd
homogeneous dimension required by the numerical C.4 budget. -/
noncomputable section
namespace Froberg
open Module Filter
open scoped Topology
variable {K : Type} [Field K] [Infinite K]
variable {h m d q f u : ℕ}

theorem odd_biform_quotient_finrank_le_count (hh : 0 < h) (hm : 0 < m)
    (S : Submodule K (biformParitySpace K h m d 1)) :
    finrank K (biformParitySpace K h m d 1 ⧸ S)≤oddCoefficientCount d h m := by
  apply S.finrank_quotient_le.trans
  exact le_of_eq (finrank_odd_biform_space hh hm)

theorem odd_background_source_finrank_le_count (hh : 0 < h) (hm : 0 < m)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :
    finrank K (oddCoefficientSpace
      ((fun j => (blockWeight h m j : ZMod 2)) ∘ finSumFinEquiv.symm)
      (backgroundEnumeratedForms Q F G))≤oddCoefficientCount d h m := by
  rw [←(oddBackgroundSourceEquiv Q F G).finrank_eq]
  exact odd_biform_quotient_finrank_le_count hh hm _

theorem odd_biform_quotient_shift_lower_order {d : ℕ} (hd : 0 < d) (hh : 0 < h) (z : ℕ)
    (S : (m : ℕ) → Submodule K (biformParitySpace K h (m+z) d 1)) :
    Tendsto (fun m : ℕ => (finrank K (biformParitySpace K h (m+z) d 1 ⧸ S m) : ℝ)/(m : ℝ)^d)
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) _
    (normalized_limit_shift (oddCoefficientCount_lower_order hd h) z)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  exact div_le_div_of_nonneg_right (by exact_mod_cast
    odd_biform_quotient_finrank_le_count hh (show 0 < m+z by omega) (S m)) (by positivity)

end Froberg
