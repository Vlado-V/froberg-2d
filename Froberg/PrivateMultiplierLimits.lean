module

public import Froberg.PrivateColumnDensity
public import Froberg.NormalizedLimits

@[expose] public section

/-! Asymptotics of the conservative private-column multiplier count. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

def privateMultiplierLowerCount (a z s b : ℕ) : ℕ :=
  (a+z+s).choose (s+1) -
    ((a+s).choose (s+1) + z*(a+s-1).choose s + b*(a+z))

theorem private_nat_tendsto_atTop_of_positive_ratio (a : ℕ → ℕ) {σ : ℝ} (hσ : 0<σ)
    (ha : Tendsto (fun n : ℕ => (a n : ℝ)/(n : ℝ)) atTop (𝓝 σ)) :
    Tendsto a atTop atTop := by
  have h := Filter.Tendsto.pos_mul_atTop hσ ha (tendsto_natCast_atTop_atTop (R := ℝ))
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  exact div_mul_cancel₀ _ hn0

theorem private_multiplier_raw_limit {s : ℕ} (hs : 2≤ s) (b : ℕ) (a z : ℕ → ℕ)
    (hsplit : ∀ᶠ n : ℕ in atTop, a n+z n=n)
    (ha : Tendsto (fun n : ℕ => (a n : ℝ)/(n : ℝ)) atTop
      (𝓝 (limitingCoreFraction (s+1)))) :
    Tendsto (fun n : ℕ =>
      (((n+s).choose (s+1) : ℝ) -
        (((a n+s).choose (s+1) : ℝ) + (z n : ℝ)*(a n+s-1).choose s + (b : ℝ)*n)) /
          (n : ℝ)^(s+1)) atTop
      (𝓝 (privateColumnDensity (s+1) / ((s+1).factorial : ℝ))) := by
  let σ := limitingCoreFraction (s+1)
  have hσ := limitingCoreFraction_bounds (show 3≤ s+1 by omega)
  have hatop := private_nat_tendsto_atTop_of_positive_ratio a hσ.1 ha
  have hid : Tendsto (fun n : ℕ => (n : ℝ)/(n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [pow_one,one_mul] using scaled_power_normalized_limit (1 : ℝ) 1
  have hz : Tendsto (fun n : ℕ => (z n : ℝ)/(n : ℝ)) atTop (𝓝 (1-σ)) := by
    apply (hid.sub ha).congr'
    filter_upwards [hsplit] with n hn
    have heq : (a n : ℝ)+(z n : ℝ)=(n : ℝ) := by exact_mod_cast hn
    rw [← heq, add_div]
    ring
  have hwhole := scaled_index_monomial_limit (fun n : ℕ => n) 1 (s+1) tendsto_id hid
  have hcore := scaled_index_monomial_limit a σ (s+1) hatop ha
  have hnear := hz.mul (scaled_index_monomial_limit a σ s hatop ha)
  have hprivate : Tendsto (fun n : ℕ => ((b : ℝ)*n)/(n : ℝ)^(s+1)) atTop (𝓝 (0 : ℝ)) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (b : ℝ)) atTop (𝓝 (b : ℝ))).div_atTop
      (nat_power_tendsto_atTop s (by omega))
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
    rw [pow_succ]
    field_simp
  have hnear' : Tendsto (fun n : ℕ => ((z n : ℝ)*(a n+s-1).choose s)/(n : ℝ)^(s+1))
      atTop (𝓝 ((1-σ)*(σ^s/(s.factorial : ℝ)))) := by
    simpa only [div_mul_div_comm,← pow_succ'] using hnear
  simp only [← Nat.add_assoc,Nat.add_sub_cancel,one_pow] at hwhole hcore
  have h := hwhole.sub ((hcore.add hnear').add hprivate)
  simp only [add_zero] at h
  have hc : 1/((s+1).factorial : ℝ) -
      (σ^(s+1)/((s+1).factorial : ℝ)+(1-σ)*(σ^s/(s.factorial : ℝ))) =
      privateColumnDensity (s+1)/((s+1).factorial : ℝ) := by
    unfold privateColumnDensity
    simp only [Nat.add_sub_cancel]
    rw [Nat.factorial_succ]
    push_cast
    have hs0 : (s.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero s
    have hs1 : (s : ℝ)+1≠0 := by positivity
    dsimp only [σ]
    field_simp
    <;> ring
  rw [hc] at h
  simpa only [sub_div,add_div] using h

theorem private_multiplier_count_limit {s : ℕ} (hs : 2≤ s) (b : ℕ) (a z : ℕ → ℕ)
    (hsplit : ∀ᶠ n : ℕ in atTop, a n+z n=n)
    (ha : Tendsto (fun n : ℕ => (a n : ℝ)/(n : ℝ)) atTop
      (𝓝 (limitingCoreFraction (s+1)))) :
    Tendsto (fun n : ℕ => (privateMultiplierLowerCount (a n) (z n) s b : ℝ)/(n : ℝ)^(s+1))
      atTop (𝓝 (privateColumnDensity (s+1)/((s+1).factorial : ℝ))) := by
  have hraw := private_multiplier_raw_limit hs b a z hsplit ha
  have hc : 0<privateColumnDensity (s+1)/((s+1).factorial : ℝ) := by
    have hp := privateColumnDensity_lower_bound (show 3≤ s+1 by omega)
    exact div_pos (by linarith) (by exact_mod_cast Nat.factorial_pos (s+1))
  have hpos := hraw.eventually (lt_mem_nhds hc)
  apply hraw.congr'
  filter_upwards [hsplit,hpos,eventually_gt_atTop (0 : ℕ)] with n hn hpn hn0
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn0
  have hbudgetR := (div_pos_iff_of_pos_right (pow_pos hnR (s+1))).mp hpn
  have hbudget : (a n+s).choose (s+1)+z n*(a n+s-1).choose s+b*n ≤ (n+s).choose (s+1) := by
    exact_mod_cast (show (((a n+s).choose (s+1) : ℝ)+(z n : ℝ)*(a n+s-1).choose s+(b : ℝ)*n) ≤
      ((n+s).choose (s+1) : ℝ) by linarith)
  simp only [privateMultiplierLowerCount,hn,Nat.cast_sub hbudget,Nat.cast_add,Nat.cast_mul]

theorem private_multiplier_eventually_above_critical {s : ℕ} (hs : 2≤ s) (b : ℕ) (a z : ℕ → ℕ)
    (hsplit : ∀ᶠ n : ℕ in atTop, a n+z n=n)
    (ha : Tendsto (fun n : ℕ => (a n : ℝ)/(n : ℝ)) atTop
      (𝓝 (limitingCoreFraction (s+1)))) :
    ∀ᶠ n : ℕ in atTop,
      criticalRatio (s+1)/((s+1).factorial : ℝ) <
        (privateMultiplierLowerCount (a n) (z n) s b : ℝ)/(n : ℝ)^(s+1) := by
  have hgap := div_lt_div_of_pos_right (criticalRatio_lt_privateColumnDensity (show 3≤ s+1 by omega))
    (show (0 : ℝ)<(s+1).factorial by exact_mod_cast Nat.factorial_pos (s+1))
  exact (private_multiplier_count_limit hs b a z hsplit ha).eventually (lt_mem_nhds hgap)

end Froberg
