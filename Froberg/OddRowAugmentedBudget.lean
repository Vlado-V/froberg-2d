module

public import Froberg.OddRowAugmentedConstants
public import Froberg.RoundingLimits

@[expose] public section

/-! The higher odd rows retain an explicit extra scalar family of density
1/(100*(2d)!), as required for the projected expansion argument. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem odd_row_augmented_factorial_gap {d b h : ℕ} (hd : 3≤d) (hb : 3≤b) (hbd : b≤d)
    (hh : 0<h) :
    (criticalRatio d/(d.factorial : ℝ)+oddRowExtraDensity d)*
        (((h+b-1).choose b : ℝ)*((d-b).factorial : ℝ)⁻¹) +
      ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))*
        (((h+(b-1)-1).choose (b-1) : ℝ)*((d-b+1).factorial : ℝ)⁻¹) <
      ((h+b-1).choose b : ℝ)*((2*d-b).factorial : ℝ)⁻¹ := by
  have hp : (0 : ℝ)<(h+b-1).choose b := by
    exact_mod_cast Nat.choose_pos (show b≤h+b-1 by omega)
  have hden : (0 : ℝ)<(h : ℝ)+b-1 := by
    have : (0 : ℝ)<h := by exact_mod_cast hh
    have : (3 : ℝ)≤b := by exact_mod_cast hb
    linarith
  have he := consecutive_monomial_counts hh (show 0<b by omega)
  have hg := oddRow_augmented_leading_ratio_lt hd hb hbd hh
  simp only [choose_real_factorial (show d-1≤2*d-b by omega),
    choose_real_factorial (show d≤2*d-b by omega),
    show 2*d-b-(d-1)=d-b+1 by omega,
    show 2*d-b-d=d-b by omega] at hg
  have htarget : (0 : ℝ)<(2*d-b).factorial := by positivity
  apply (mul_lt_mul_iff_left₀ htarget).mp
  have hscaled := mul_lt_mul_of_pos_right hg hp
  have hsolve : ((h+(b-1)-1).choose (b-1) : ℝ)=
      ((h+b-1).choose b : ℝ)*b/((h : ℝ)+b-1) := by
    apply (eq_div_iff hden.ne').mpr
    simpa only [mul_comm] using he
  rw [hsolve]
  convert hscaled using 1 <;> field_simp [factorial_real_ne_zero,hden.ne'] <;> ring


theorem eventually_augmented_higher_odd_row_budget {d b h : ℕ}
    (hd : 3≤d) (hb : 3≤b) (hbd : b≤d) (hh : 0<h)
    (qS qO : ℕ → ℕ)
    (hS : Tendsto (fun n : ℕ => (qS n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ))))
    (hO : Tendsto (fun n : ℕ => (qO n : ℝ)/(n : ℝ)^(d-1)) atTop
      (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ)))) :
    ∀ᶠ n : ℕ in atTop,
      (qS n+⌊oddRowExtraDensity d*(n : ℝ)^d⌋₊+(h+b-1).choose b*(n+(d-b)-1).choose (d-b))*
          ((h+b-1).choose b*(n+(d-b)-1).choose (d-b)) +
        (qO n+(h+(b-1)-1).choose (b-1)*(n+(d-b+1)-1).choose (d-b+1))*
          ((h+(b-1)-1).choose (b-1)*(n+(d-b+1)-1).choose (d-b+1)) ≤
        (h+b-1).choose b*(n+(2*d-b)-1).choose (2*d-b) := by
  let Q : ℕ → ℕ := fun n => qS n+⌈oddRowExtraDensity d*(n : ℝ)^d⌉₊
  have he := ceil_normalized_limit (fun n : ℕ => oddRowExtraDensity d*(n : ℝ)^d)
    (by omega : 0<d) (oddRowExtraDensity d)
    (Eventually.of_forall fun n => mul_nonneg (oddRowExtraDensity_pos d).le (by positivity))
    (scaled_power_normalized_limit (oddRowExtraDensity d) d)
  have hQ : Tendsto (fun n : ℕ => (Q n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ)+oddRowExtraDensity d)) := by
    simpa only [Q,Nat.cast_add,add_div] using hS.add he
  filter_upwards [eventually_higher_odd_row_budget_of_gap hd hb hbd hh Q qO _ _
    (odd_row_augmented_factorial_gap hd hb hbd hh) hQ hO] with n hn
  have hfc : ⌊oddRowExtraDensity d*(n : ℝ)^d⌋₊≤⌈oddRowExtraDensity d*(n : ℝ)^d⌉₊ :=
    Nat.floor_le_ceil _
  dsimp only [Q] at hn
  apply le_trans ?_ hn
  gcongr <;> exact hfc


end Froberg
