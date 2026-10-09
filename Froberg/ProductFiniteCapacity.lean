module

public import Froberg.ProductFiniteMargins

@[expose] public section

/-! Prescribed Section 5 counts satisfy the exact finite B.4 product
capacities, uniformly for every active layer in degrees at least nine. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

def diagonalProductCount (d j h m : ℕ) : ℕ :=
  diagonalOutputCount d j h*((m/2).choose (d-j)/2)

def crossProductCount (d j h m : ℕ) : ℕ :=
  ((h/2+j-1).choose j-deletedTargetCount d h)*(m/2+(d-j)-1).choose (d-j)

theorem diagonalProductCount_le_cross {d j h m : ℕ} (hj : 1 ≤ j) (hjd : j < d) :
    diagonalProductCount d j h m ≤ crossProductCount d j h m := by
  apply Nat.mul_le_mul
  · exact Nat.sub_le_sub_right (Nat.choose_le_choose j (by omega)) _
  · exact (Nat.div_le_self _ _).trans (Nat.choose_le_choose (d-j) (by omega))

theorem eventually_product_capacity_majorant {d j : ℕ} (hd : 9 ≤ d)
    (hj : j ∈ activeEvenIndices d) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      ⌈(253/250 : ℝ)*intermediateDensity d j*(h : ℝ)^j*(m : ℝ)^(d-j)⌉₊ ≤
        diagonalProductCount d j h m := by
  have hb := activeEvenIndices_bounds (show 3 ≤ d by omega) hj
  apply eventually_diagonal_capacity_of_density hd hb.1 (by omega)
  · unfold intermediateDensity
    split_ifs
    · have hp := countTauFour_le_gamma d
      have hp' := countTauFour_pos (show 3 ≤ d by omega)
      exact mul_nonneg (by norm_num) (lt_of_lt_of_le hp' hp).le
    · exact mul_nonneg (by norm_num) (higherCountGamma_pos d j).le
  · by_cases hj2 : j=2
    · subst j
      simpa [intermediateDensity] using quadratic_finite_product_density_gap hd
    · have hj4 : 4 ≤ j := by obtain ⟨k,hk⟩ := hb.2.2; omega
      have hactive : j ∈ activeHigherIndices d := Finset.mem_filter.mpr ⟨hj,hj4⟩
      simpa only [intermediateDensity,if_neg hj2] using higher_finite_product_density_gap hd hactive

theorem eventually_quadratic_finite_product_capacity {d : ℕ} (hd : 9 ≤ d) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop, ∀ r : ℕ,
      (r : ℝ) < countBeta d*(h : ℝ)^2*(m : ℝ)^(d-2) →
      r ≤ diagonalProductCount d 2 h m ∧ r ≤ crossProductCount d 2 h m := by
  have he := eventually_product_capacity_majorant hd (two_mem_activeEvenIndices (by omega))
  filter_upwards [he] with h hh
  filter_upwards [hh] with m hm
  intro r hr
  have hγ : 0 < countGammaTwo d := lt_of_lt_of_le (countTauFour_pos (by omega)) (countTauFour_le_gamma d)
  have hcoeff : countBeta d ≤ (253/250 : ℝ)*countGammaTwo d := by unfold countBeta; nlinarith
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (Nat.cast_nonneg h) 2))
    (pow_nonneg (Nat.cast_nonneg m) (d-2))
  have hrceil : r ≤ ⌈(253/250 : ℝ)*countGammaTwo d*(h : ℝ)^2*(m : ℝ)^(d-2)⌉₊ := by
    exact_mod_cast hr.le.trans (hscaled.trans (Nat.le_ceil _))
  have hrdiag : r ≤ diagonalProductCount d 2 h m :=
    hrceil.trans (by simpa [intermediateDensity] using hm)
  exact ⟨hrdiag,hrdiag.trans (diagonalProductCount_le_cross (by omega) (by omega))⟩

theorem eventually_higher_finite_product_capacity {d j : ℕ} (hd : 9 ≤ d)
    (hj : j ∈ activeHigherIndices d) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      higherGeneratorCount d h m j ≤ diagonalProductCount d j h m ∧
      higherGeneratorCount d h m j ≤ crossProductCount d j h m := by
  have he := eventually_product_capacity_majorant hd (Finset.mem_filter.mp hj).1
  have hb := activeEvenIndices_bounds (show 3 ≤ d by omega) (Finset.mem_filter.mp hj).1
  have hj4 := (Finset.mem_filter.mp hj).2
  filter_upwards [he] with h hh
  filter_upwards [hh] with m hm
  have hcoeff : (101/100 : ℝ)*higherCountGamma d j ≤ (253/250 : ℝ)*higherCountGamma d j := by
    nlinarith [higherCountGamma_pos d j]
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (Nat.cast_nonneg h) j))
    (pow_nonneg (Nat.cast_nonneg m) (d-j))
  have hrdiag : higherGeneratorCount d h m j ≤ diagonalProductCount d j h m :=
    (Nat.ceil_mono hscaled).trans (by simpa only [intermediateDensity,if_neg (show j≠2 by omega)] using hm)
  exact ⟨hrdiag,hrdiag.trans (diagonalProductCount_le_cross (by omega) hb.2.1)⟩

end Froberg
