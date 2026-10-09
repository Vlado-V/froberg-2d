module

public import Froberg.AdjacentCriticalRatio
public import Froberg.CapacityProductIdentity

@[expose] public section

/-! Exact binomial costs for the higher odd coefficient rows. -/
noncomputable section
namespace Froberg

def oddRowBinomialCost (d b : ℕ) : ℕ :=
  b*(2*d-b).choose (d-1)+(2*d-b).choose d

theorem oddRowBinomialCost_step {d b : ℕ} (hd : 2≤d) (hb : b+1≤d) :
    oddRowBinomialCost d b = oddRowBinomialCost d (b+1)+
      b*(2*d-b-1).choose (d-2) := by
  have h₁ := Nat.choose_succ_succ (2*d-b-1) (d-2)
  have h₂ := Nat.choose_succ_succ (2*d-b-1) (d-1)
  simp only [Nat.succ_eq_add_one,show 2*d-b-1+1=2*d-b by omega,
    show d-2+1=d-1 by omega,show d-1+1=d by omega] at h₁ h₂
  unfold oddRowBinomialCost
  rw [h₁,h₂,show 2*d-(b+1)=2*d-b-1 by omega]
  ring

theorem oddRowBinomialCost_three {d : ℕ} (hd : 3≤d) :
    oddRowBinomialCost d 3 = centralHalfBinomial d := by
  have h₁ := Nat.choose_succ_succ (2*d-3) (d-2)
  have h₂ := Nat.choose_succ_succ (2*d-3) (d-1)
  have h₃ := Nat.choose_succ_succ (2*d-2) (d-2)
  simp only [Nat.succ_eq_add_one,show 2*d-3+1=2*d-2 by omega,
    show 2*d-2+1=2*d-1 by omega,show d-2+1=d-1 by omega,
    show d-1+1=d by omega] at h₁ h₂ h₃
  have hs₁ : (2*d-3).choose (d-2)=(2*d-3).choose (d-1) :=
    Nat.choose_symm_of_eq_add (by omega)
  have hs₂ : (2*d-2).choose (d-2)=(2*d-2).choose d :=
    Nat.choose_symm_of_eq_add (by omega)
  unfold oddRowBinomialCost centralHalfBinomial
  omega

theorem oddRowBinomialCost_le {d b : ℕ} (hd : 3≤d) (hb : 3≤b) (hbd : b≤d) :
    oddRowBinomialCost d b≤centralHalfBinomial d := by
  revert hbd
  induction b,hb using Nat.le_induction with
  | base => intro _; exact (oddRowBinomialCost_three hd).le
  | succ b hb ih =>
    intro hbd
    have hs := oddRowBinomialCost_step (by omega : 2≤d) hbd
    exact (show oddRowBinomialCost d (b+1)≤oddRowBinomialCost d b by omega).trans
      (ih (by omega))

theorem oddRow_leading_ratio_lt {d b h : ℕ} (hd : 3≤d) (hb : 3≤b) (hbd : b≤d)
    (hh : 0<h) :
    criticalRatio d*((b : ℝ)*h/((h : ℝ)+b-1)*((2*d-b).choose (d-1) : ℝ)+
      ((2*d-b).choose d : ℝ)) < 1 := by
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

theorem oddEndpoint_leading_ratio_lt {d h : ℕ} (hd : 3≤d) (hh : 0<h) :
    ((d : ℝ)+1)*h*criticalRatio d/((h : ℝ)+d)<1 := by
  have hρ := (criticalRatio_bounds (by omega : 2≤d)).1
  have hH : (d : ℝ)+1≤centralHalfBinomial d := by
    exact_mod_cast centralHalfBinomial_ge_succ (by omega : 2≤d)
  have hsmall : ((d : ℝ)+1)*criticalRatio d<1 := by
    have hm := mul_le_mul_of_nonneg_right hH hρ.le
    have hb := criticalRatio_sharp_bound hd
    linarith
  have hhR : (0 : ℝ)<h := by exact_mod_cast hh
  apply (div_lt_iff₀ (by positivity : 0<(h : ℝ)+d)).mpr
  have hm := mul_lt_mul_of_pos_right hsmall hhR
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

end Froberg
