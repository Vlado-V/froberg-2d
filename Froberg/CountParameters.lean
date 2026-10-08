import Froberg.CriticalRatioBounds

/-! The strict numerical margins in the generator-count construction. -/
noncomputable section
namespace Froberg

theorem middle_binomial_four_lt_half {d : ℕ} (hd : 3 ≤ d) :
    4 * (2 * d - 4).choose (d - 2) < centralHalfBinomial d := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hd
  have hcentral := centralBinomial_eq_twice_half (d := t + 2) (by omega)
  have h₁ := Nat.choose_succ_succ (2 * t + 4) (t + 1)
  have h₂ := Nat.choose_succ_succ (2 * t + 2) t
  have h₃ := Nat.choose_succ_succ (2 * t + 3) t
  have hmono := Nat.choose_le_succ (2 * t + 2) t
  have hstep := Nat.choose_succ_right_eq (2 * t + 2) t
  have hpos : 0 < (2 * t + 2).choose (t + 1) := Nat.choose_pos (by omega)
  have harith : 2 * t + 2 - t = t + 2 := by omega
  rw [harith] at hstep
  have hbound : (2 * t + 2).choose (t + 1) ≤ 2 * (2 * t + 2).choose t := by
    by_contra hh
    have hm := Nat.mul_lt_mul_of_pos_right (show
      2 * (2 * t + 2).choose t < (2 * t + 2).choose (t + 1) by omega)
      (show 0 < t + 1 by omega)
    nlinarith [Nat.zero_le ((2 * t + 2).choose t * t)]
  unfold centralHalfBinomial at hcentral ⊢
  have hi : 2 * (t + 2) = 2 * t + 4 := by omega
  have hj : 2 * (t + 2) - 1 = 2 * t + 3 := by omega
  have hk : t + 2 - 1 = t + 1 := by omega
  rw [hj, hi, hk] at hcentral
  have htop : 2 * (3 + t) - 1 = 2 * t + 5 := by omega
  have hbot : 3 + t - 1 = t + 2 := by omega
  have htop' : 2 * (3 + t) - 4 = 2 * t + 2 := by omega
  have hbot' : 3 + t - 2 = t + 1 := by omega
  rw [htop, hbot, htop', hbot']
  simp only [Nat.succ_eq_add_one] at h₁ h₂ h₃ hmono
  nlinarith

theorem quadratic_critical_ratio_gt : (2 / 11 : ℝ) < criticalRatio 2 := by
  have hid := criticalRatio_identity (d := 2) (by omega)
  have hb := criticalRatio_bounds (d := 2) (by omega)
  norm_num [centralHalfBinomial] at hid
  by_contra h
  have hh : (9 / 11 : ℝ) ≤ 1 - criticalRatio 2 := by linarith
  have hs := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 9 / 11) hh
  nlinarith

theorem critical_ratio_middle_gap {d : ℕ} (hd : 3 ≤ d) :
    criticalRatio d * ((2 * d - 4).choose (d - 2) : ℝ) < criticalRatio 2 := by
  have hc : 4 * ((2 * d - 4).choose (d - 2) : ℝ) < (centralHalfBinomial d : ℝ) := by
    exact_mod_cast middle_binomial_four_lt_half hd
  have hr := (criticalRatio_bounds (d := d) (by omega)).1
  have hmul := mul_lt_mul_of_pos_left hc hr
  have hsharp := criticalRatio_sharp_bound hd
  have htwo := quadratic_critical_ratio_gt
  nlinarith

def countTauFour (d : ℕ) : ℝ := criticalRatio 2 /
  (2 * ((d - 2).factorial : ℝ) * ((2 * d - 4).choose (d - 2) : ℝ))

def countGammaTwo (d : ℕ) : ℝ :=
  if d ≤ 8 then max
    (9 / (32 * ((d - 2).factorial : ℝ) * ((2 * d - 2).choose (d - 2) : ℝ)))
    (max (1 / (6 * ((d - 2).factorial : ℝ) * ((2 * d - 3).choose (d - 2) : ℝ)))
      (countTauFour d))
  else countTauFour d

def countAlpha (d : ℕ) : ℝ := (101 / 100) * countGammaTwo d
def countBeta (d : ℕ) : ℝ := (1011 / 1000) * countGammaTwo d

theorem countTauFour_pos {d : ℕ} (hd : 3 ≤ d) : 0 < countTauFour d := by
  have hr := (criticalRatio_bounds (d := 2) (by omega)).1
  have hf : (0 : ℝ) < (d - 2).factorial := by exact_mod_cast Nat.factorial_pos (d - 2)
  have hc : (0 : ℝ) < (2 * d - 4).choose (d - 2) := by
    exact_mod_cast Nat.choose_pos (show d - 2 ≤ 2 * d - 4 by omega)
  exact div_pos hr (mul_pos (mul_pos (by norm_num) hf) hc)

theorem countTauFour_le_gamma (d : ℕ) : countTauFour d ≤ countGammaTwo d := by
  unfold countGammaTwo
  split_ifs
  · exact (le_max_right _ _).trans (le_max_right _ _)
  · rfl

theorem countAlpha_lt_beta {d : ℕ} (hd : 3 ≤ d) : countAlpha d < countBeta d := by
  have hγ : 0 < countGammaTwo d := (countTauFour_pos hd).trans_le (countTauFour_le_gamma d)
  unfold countAlpha countBeta
  linarith

theorem countAlpha_margin {d : ℕ} (hd : 3 ≤ d) :
    (d : ℝ) * ((d : ℝ) - 1) * criticalRatio d / (2 * (d.factorial : ℝ)) < countAlpha d := by
  have hτpos := countTauFour_pos hd
  have hγ := countTauFour_le_gamma d
  have hfac : (d.factorial : ℝ) = (d : ℝ) * ((d : ℝ) - 1) * ((d - 2).factorial : ℝ) := by
    have h₁ : d = (d - 1) + 1 := by omega
    have h₂ : d - 1 = (d - 2) + 1 := by omega
    conv_lhs => rw [h₁, Nat.factorial_succ, ← h₁, h₂, Nat.factorial_succ, ← h₂]
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    ring
  have hf : (0 : ℝ) < (d - 2).factorial := by exact_mod_cast Nat.factorial_pos (d - 2)
  have hc : (0 : ℝ) < (2 * d - 4).choose (d - 2) := by
    exact_mod_cast Nat.choose_pos (show d - 2 ≤ 2 * d - 4 by omega)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hτ : criticalRatio d / (2 * ((d - 2).factorial : ℝ)) < countTauFour d := by
    unfold countTauFour
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    have hm := mul_lt_mul_of_pos_left (critical_ratio_middle_gap hd)
      (show 0 < 2 * ((d - 2).factorial : ℝ) by positivity)
    nlinarith
  have hid : (d : ℝ) * ((d : ℝ) - 1) * criticalRatio d / (2 * (d.factorial : ℝ)) =
      criticalRatio d / (2 * ((d - 2).factorial : ℝ)) := by
    rw [hfac]
    field_simp
  rw [hid]
  unfold countAlpha
  linarith

end Froberg
