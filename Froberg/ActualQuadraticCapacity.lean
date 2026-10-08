import Froberg.QuadraticCapacityParameters
import Froberg.HigherCapacityParameters

/-! The quadratic row capacity for the actual prepared scalar and layer
counts; fixed appended columns use the same sparse block count. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module Filter
open scoped Topology
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ]

theorem eventually_actual_quadratic_capacity {d : ℕ} (hd : 3≤d) :
    ∀ᶠ h : ℕ in atTop,∀ (σ : Type*) [Fintype σ],
      ∀ (O : ℕ → Submodule K (MvPolynomial σ K)),
      finrank K (O 2)=quadraticOutputDimension d h →
      ∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2)) →
      ∀ᶠ n : ℕ in atTop,
        QuadraticRowCapacity n d (upperCount n d)
          (fullSparseBlockCount (countBeta d) 2 (d-2) h) (activeEvenIndices d)
          (targetLayerCount d h n (e n+extra)) O := by
  filter_upwards [eventually_quadratic_capacity (K := K) hd] with h hh
  intro σ inst O hO extra e he
  have hr := targetLayerLabel_count_limit hd h extra e he
  have hcap := hh σ O hO (activeEvenIndices d) (fun n => upperCount n d)
    (fun n => targetLayerCount d h n (e n+extra)) hr extra
  filter_upwards [hcap,he] with n hn hen
  apply hn
  have heceil : e n≤⌈countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2)⌉₊ := by
    exact_mod_cast hen.le.trans (Nat.le_ceil _)
  simpa only [targetLayerCount,ite_true] using Nat.add_le_add_right heceil extra

end Froberg.PreparedParameters
