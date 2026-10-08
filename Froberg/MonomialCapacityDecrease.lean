import Froberg.ProfileCapacityDrop

/-! The capacity decrease in one target profile has uniform mass in each
source row of the actual monomial transport. -/
noncomputable section
namespace Froberg
open Finset MonomialExpansion

lemma monomialProfileJoint_fiber_sum {a z s : ℕ} (ha : 0 < a) (hz : 0 < z)
    (P : Option (Fin s) → Fin (2*s+1) → ℝ)
    (hPzero : ∀ i j, ¬profileAllowed i j → P i j = 0)
    (α : Σ i, SourceMonomialFiber a z s i) (j : Fin (2*s+1)) :
    (∑ β : TargetMonomialFiber a z s j, monomialProfileJoint P α ⟨j, β⟩) =
      P α.1 j / (Fintype.card (SourceMonomialFiber a z s α.1) : ℝ) := by
  simp only [monomialProfileJoint, fiberTransport, ← mul_sum]
  by_cases hj : profileAllowed α.1 j
  · rw [localMonomialCoupling_row ha hz α.1 j hj]
    ring
  · rw [hPzero α.1 j hj]
    simp

lemma monomialProfileJoint_weighted_profile_sum {a z s : ℕ} (ha : 0 < a) (hz : 0 < z)
    (P : Option (Fin s) → Fin (2*s+1) → ℝ)
    (hPzero : ∀ i j, ¬profileAllowed i j → P i j = 0)
    (α : Σ i, SourceMonomialFiber a z s i) (w : Fin (2*s+1) → ℝ) :
    (∑ β : Σ j, TargetMonomialFiber a z s j, monomialProfileJoint P α β * w β.1) =
      (∑ j, P α.1 j * w j) / (Fintype.card (SourceMonomialFiber a z s α.1) : ℝ) := by
  rw [Fintype.sum_sigma]
  simp_rw [← sum_mul, monomialProfileJoint_fiber_sum ha hz P hPzero α]
  simp only [div_mul_eq_mul_div, ← sum_div]

/-- The decrease coefficient is at least ε/H for every source atom. -/
theorem monomial_capacity_decrease {a z s : ℕ} (ha : 0 < a) (hz : 0 < z) (hs : 0 < s)
    (P : Option (Fin s) → Fin (2*s+1) → ℝ) (p : Option (Fin s) → ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j)
    (hPzero : ∀ i j, ¬profileAllowed i j → P i j = 0)
    (hp : ∀ i, p i ≤ 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hPlower : ∀ i j, profileAllowed i j → ε ≤ P i j)
    (α : Σ i, SourceMonomialFiber a z s i) :
    (ε / profileAmbientCapacity s) *
        (p α.1 / (Fintype.card (SourceMonomialFiber a z s α.1) : ℝ)) ≤
      ∑ β : Σ j, TargetMonomialFiber a z s j,
        monomialProfileJoint P α β * profileCapacityDrop s α.1 β.1 := by
  rw [monomialProfileJoint_weighted_profile_sum ha hz P hPzero]
  have hH := profileAmbientCapacity_pos s
  have hcap : (0 : ℝ) < Fintype.card (SourceMonomialFiber a z s α.1) := by
    exact_mod_cast sourceMonomialFiber_card_pos ha hz α.1
  have hnonneg (j : Fin (2*s+1)) : 0 ≤ P α.1 j * profileCapacityDrop s α.1 j := by
    by_cases hj : profileAllowed α.1 j
    · exact mul_nonneg (hP0 _ _) (profileCapacityDrop_nonneg hs _ _ hj)
    · rw [hPzero _ _ hj, zero_mul]
  have hgood : ε / profileAmbientCapacity s ≤
      P α.1 (capacityDropTarget hs α.1) * profileCapacityDrop s α.1 (capacityDropTarget hs α.1) := by
    calc
      _ = ε * (1 / profileAmbientCapacity s) := by ring
      _ ≤ _ := mul_le_mul (hPlower _ _ (capacityDropTarget_allowed hs α.1))
        (profileCapacityDrop_target_lower hs α.1) (by positivity) (hP0 _ _)
  have hsum : ε / profileAmbientCapacity s ≤ ∑ j, P α.1 j * profileCapacityDrop s α.1 j :=
    hgood.trans (single_le_sum (fun j _ => hnonneg j) (mem_univ _))
  have hh := mul_le_mul_of_nonneg_left (hp α.1) (div_nonneg hε hH.le)
  have hnum : (ε / profileAmbientCapacity s) * p α.1 ≤
      ∑ j, P α.1 j * profileCapacityDrop s α.1 j := by
    simp only [mul_one] at hh
    exact hh.trans hsum
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hnum hcap.le

end Froberg
