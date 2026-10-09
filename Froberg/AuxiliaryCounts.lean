module

public import Froberg.CountConstruction

@[expose] public section

/-! The explicit higher-bidegree and tail counts in Section 5, and their
proved lower order relative to the main outer count. -/
noncomputable section
namespace Froberg
open Filter Finset
open scoped Topology

def activeEvenIndices (d : ℕ) : Finset ℕ :=
  if d ≤ 8 then ({2, 4} : Finset ℕ).filter (fun j => j < d)
  else (range (2 * ((d + 3) / 4) + 1)).filter (fun j => Even j ∧ 2 ≤ j)

def activeHigherIndices (d : ℕ) : Finset ℕ :=
  (activeEvenIndices d).filter (fun j => 4 ≤ j)

theorem activeEvenIndices_bounds {d j : ℕ} (hd : 3 ≤ d) (hj : j ∈ activeEvenIndices d) :
    2 ≤ j ∧ j < d ∧ Even j := by
  unfold activeEvenIndices at hj
  split_ifs at hj with hd8
  · simp only [mem_filter, mem_insert, mem_singleton] at hj
    rcases hj with ⟨rfl | rfl, hlt⟩ <;> norm_num at * <;> omega
  · simp only [mem_filter, mem_range] at hj
    exact ⟨hj.2.2, by omega, hj.2.1⟩

theorem two_mem_activeEvenIndices {d : ℕ} (hd : 3 ≤ d) : 2 ∈ activeEvenIndices d := by
  unfold activeEvenIndices
  split_ifs <;> simp only [mem_filter, mem_insert, mem_singleton, mem_range]
  · exact ⟨Or.inl trivial, by omega⟩
  · exact ⟨by omega, by decide, le_rfl⟩

def higherCountGamma (d j : ℕ) : ℝ :=
  if j = 4 then ((d - 1).factorial : ℝ) / (120 * ((2 * d - 5).factorial : ℝ))
  else ((j - 4).factorial : ℝ) * ((d - j + 4).factorial : ℝ) /
    (((2 * j - 4).factorial : ℝ) * ((2 * d - 2 * j + 4).factorial : ℝ))

theorem higherCountGamma_pos (d j : ℕ) : 0 < higherCountGamma d j := by
  unfold higherCountGamma
  split_ifs <;> positivity

def higherGeneratorCount (d h m j : ℕ) : ℕ :=
  ⌈(101 / 100 : ℝ) * higherCountGamma d j * (h : ℝ) ^ j * (m : ℝ) ^ (d - j)⌉₊

def tailGeneratorCount (d h : ℕ) : ℕ :=
  if Odd d then ⌈2 * (h : ℝ) ^ d / ((d + 1).factorial : ℝ)⌉₊
  else (h + d - 1).choose d

def auxiliaryGeneratorCount (d h m : ℕ) : ℕ :=
  tailGeneratorCount d h + ∑ j ∈ activeHigherIndices d, higherGeneratorCount d h m j

theorem auxiliaryGeneratorCount_lower_order {d : ℕ} (hd : 3 ≤ d) (h : ℕ) :
    Tendsto (fun m : ℕ => (auxiliaryGeneratorCount d h m : ℝ) / (m : ℝ) ^ (d - 1))
      atTop (𝓝 0) := by
  apply auxiliary_counts_lower_order (activeHigherIndices d) (by omega)
    (fun j => (101 / 100 : ℝ) * higherCountGamma d j * (h : ℝ) ^ j)
    (fun j => d - j) (tailGeneratorCount d h)
  · intro j _
    exact mul_nonneg (mul_nonneg (by norm_num) (higherCountGamma_pos d j).le) (by positivity)
  · intro j hj
    have hh : 4 ≤ j := (mem_filter.mp hj).2
    omega

def adjacentCriticalCount (upper : Bool) (n d : ℕ) : ℕ :=
  if upper then upperCount n d else lowerCount n d

theorem adjacentCriticalCount_bounds (upper : Bool) (n d : ℕ) :
    lowerCount n d ≤ adjacentCriticalCount upper n d ∧
      adjacentCriticalCount upper n d ≤ upperCount n d := by
  cases upper <;> simp only [adjacentCriticalCount, Bool.false_eq_true, reduceIte]
  · exact ⟨le_rfl, lowerCount_le_upperCount n d⟩
  · exact ⟨lowerCount_le_upperCount n d, le_rfl⟩

end Froberg
