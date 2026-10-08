import Froberg.OddRowGeneralBudget

noncomputable section
namespace Froberg

theorem oddRow_leading_ratio_sharp {d b h : ℕ} (hd : 3≤d) (hb : 3≤b) (hbd : b≤d)
    (hh : 0<h) :
    criticalRatio d*((b : ℝ)*h/((h : ℝ)+b-1)*((2*d-b).choose (d-1) : ℝ)+
      ((2*d-b).choose d : ℝ)) < 13/25 := by
  have hden : 0<(h : ℝ)+b-1 := by
    have hbR : (3 : ℝ)≤b := by exact_mod_cast hb
    have hhR : (0 : ℝ)<h := by exact_mod_cast hh
    linarith
  have hfrac : (b : ℝ)*h/((h : ℝ)+b-1)≤b := by
    apply (div_le_iff₀ hden).mpr
    have hbR : (3 : ℝ)≤b := by exact_mod_cast hb
    nlinarith
  have hc : (b : ℝ)*((2*d-b).choose (d-1) : ℝ)+((2*d-b).choose d : ℝ) ≤
      centralHalfBinomial d := by exact_mod_cast oddRowBinomialCost_le hd hb hbd
  have hm := mul_le_mul_of_nonneg_right hfrac
    (show (0 : ℝ)≤(2*d-b).choose (d-1) by positivity)
  have hρ := (criticalRatio_bounds (by omega : 2≤d)).1
  have hl := mul_le_mul_of_nonneg_left (show (b : ℝ)*h/((h : ℝ)+b-1)*
      ((2*d-b).choose (d-1) : ℝ)+((2*d-b).choose d : ℝ)≤centralHalfBinomial d by linarith) hρ.le
  have hsharp := criticalRatio_sharp_bound hd
  nlinarith


def oddRowExtraDensity (d : ℕ) : ℝ := 1/(100*((2*d).factorial : ℝ))

theorem oddRowExtraDensity_pos (d : ℕ) : 0<oddRowExtraDensity d := by
  unfold oddRowExtraDensity
  positivity

theorem oddRow_extra_ratio_le {d b : ℕ} (hb : b≤d) :
    oddRowExtraDensity d*(d.factorial : ℝ)*((2*d-b).choose d : ℝ) ≤ 1/100 := by
  have hc : (2*d-b).choose d*d.factorial≤(2*d).factorial := by
    calc
      (2*d-b).choose d*d.factorial ≤
          ((2*d-b).choose d*d.factorial)*(2*d-b-d).factorial := by
        exact Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
      _ = (2*d-b).factorial := Nat.choose_mul_factorial_mul_factorial (by omega)
      _ ≤ (2*d).factorial := Nat.factorial_le (Nat.sub_le _ _)
  have hcR : ((2*d-b).choose d : ℝ)*d.factorial ≤ (2*d).factorial := by exact_mod_cast hc
  have hf : (0 : ℝ)<(2*d).factorial := by positivity
  have he : oddRowExtraDensity d*(d.factorial : ℝ)*((2*d-b).choose d : ℝ) =
      (((2*d-b).choose d : ℝ)*d.factorial)/(100*((2*d).factorial : ℝ)) := by
    unfold oddRowExtraDensity
    ring
  rw [he]
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<100*((2*d).factorial : ℝ))).mpr
  nlinarith

theorem oddRow_augmented_leading_ratio_lt {d b h : ℕ}
    (hd : 3≤d) (hb : 3≤b) (hbd : b≤d) (hh : 0<h) :
    criticalRatio d*((b : ℝ)*h/((h : ℝ)+b-1)*((2*d-b).choose (d-1) : ℝ)+
      ((2*d-b).choose d : ℝ))+
      oddRowExtraDensity d*(d.factorial : ℝ)*((2*d-b).choose d : ℝ) < 1 := by
  have h₁ := oddRow_leading_ratio_sharp hd hb hbd hh
  have h₂ := oddRow_extra_ratio_le hbd
  linarith

end Froberg
