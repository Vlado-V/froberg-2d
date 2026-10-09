module

public import Froberg.FiniteMonomialTransport

@[expose] public section

/-! Every source profile has a uniformly positive decrease of capacity
on an explicitly chosen allowed target profile. -/
noncomputable section
namespace Froberg

abbrev profileAmbientCapacity (s : ℕ) : ℝ := ((2 * s + 1).choose s : ℕ)

def capacityDropTarget {s : ℕ} (hs : 0 < s) : Option (Fin s) → Fin (2 * s + 1)
  | some _ => ⟨s, by omega⟩
  | none => ⟨s + 1, by omega⟩

lemma capacityDropTarget_allowed {s : ℕ} (hs : 0 < s) (i : Option (Fin s)) :
    profileAllowed i (capacityDropTarget hs i) := by
  cases i <;> simp only [capacityDropTarget, profileAllowed, profileSourceIndex] <;> constructor <;> omega

lemma profileTargetCapacity_le_source {s : ℕ} (i : Option (Fin s)) (j : Fin (2 * s + 1))
    (hij : profileAllowed i j) :
    profileTargetCapacity s j ≤ profileSourceCapacity (profileAmbientCapacity s) i := by
  cases i with
  | some i =>
      simp only [profileTargetCapacity, profileSourceCapacity, profileAmbientCapacity]
      linarith [Nat.cast_nonneg (j.val.choose s) (α := ℝ)]
  | none =>
      have hc : (1 : ℝ) ≤ j.val.choose s := by
        exact_mod_cast Nat.choose_pos hij.1
      simp only [profileTargetCapacity, profileSourceCapacity, profileAmbientCapacity]
      linarith

lemma profileTargetCapacity_ge_one {s : ℕ} (hs : 0 < s) (j : Fin (2 * s + 1)) :
    1 ≤ profileTargetCapacity s j := by
  have hp := profileTargetCapacity_pos hs j
  have hi : j.val.choose s < (2 * s + 1).choose s := by
    unfold profileTargetCapacity at hp
    exact_mod_cast (sub_pos.mp hp)
  have hc : (j.val.choose s : ℝ) + 1 ≤ (2 * s + 1).choose s := by exact_mod_cast hi
  unfold profileTargetCapacity
  linarith

lemma profileAmbientCapacity_pos (s : ℕ) : 0 < profileAmbientCapacity s := by
  exact_mod_cast Nat.choose_pos (show s ≤ 2 * s + 1 by omega)

lemma capacityDropTarget_gap {s : ℕ} (hs : 0 < s) (i : Option (Fin s)) :
    1 ≤ profileSourceCapacity (profileAmbientCapacity s) i -
      profileTargetCapacity s (capacityDropTarget hs i) := by
  cases i with
  | some i => simp [profileSourceCapacity, profileTargetCapacity, capacityDropTarget, profileAmbientCapacity]
  | none =>
      simp only [profileSourceCapacity, profileTargetCapacity, capacityDropTarget,
        Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_one, profileAmbientCapacity]
      have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
      linarith

def profileCapacityDrop (s : ℕ) (i : Option (Fin s)) (j : Fin (2 * s + 1)) : ℝ :=
  min (profileTargetCapacity s j)
    (profileSourceCapacity (profileAmbientCapacity s) i - profileTargetCapacity s j) /
    profileTargetCapacity s j

lemma profileCapacityDrop_nonneg {s : ℕ} (hs : 0 < s)
    (i : Option (Fin s)) (j : Fin (2 * s + 1)) (hij : profileAllowed i j) :
    0 ≤ profileCapacityDrop s i j := by
  exact div_nonneg
    (le_min (profileTargetCapacity_pos hs j).le (sub_nonneg.mpr (profileTargetCapacity_le_source i j hij)))
    (profileTargetCapacity_pos hs j).le

lemma profileCapacityDrop_target_lower {s : ℕ} (hs : 0 < s) (i : Option (Fin s)) :
    1 / profileAmbientCapacity s ≤ profileCapacityDrop s i (capacityDropTarget hs i) := by
  have hc := profileTargetCapacity_pos hs (capacityDropTarget hs i)
  have hc1 := profileTargetCapacity_ge_one hs (capacityDropTarget hs i)
  have hg := capacityDropTarget_gap hs i
  have hcH : profileTargetCapacity s (capacityDropTarget hs i) ≤ profileAmbientCapacity s := by
    unfold profileTargetCapacity profileAmbientCapacity
    linarith [Nat.cast_nonneg ((capacityDropTarget hs i).val.choose s) (α := ℝ)]
  unfold profileCapacityDrop
  calc
    1 / profileAmbientCapacity s ≤ 1 / profileTargetCapacity s (capacityDropTarget hs i) :=
      one_div_le_one_div_of_le hc hcH
    _ ≤ _ := div_le_div_of_nonneg_right (le_min hc1 hg) hc.le

end Froberg
