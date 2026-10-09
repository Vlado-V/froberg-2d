module

public import Froberg.ExtendedPrefixConvolution
public import Froberg.UpperEndpointConvolution
public import Froberg.SmallDegreeCapacities
public import Froberg.BlockParameters

@[expose] public section

/-! The actual allowed dimension of the quadratic output space leaves room
for the row-three and row-four witnesses. -/
noncomputable section
namespace Froberg
open Filter Module
open scoped Topology

def quadraticOutputDimension (d h : ℕ) : ℕ := (h+1).choose 2-deletedTargetCount d h

def quadraticOutputDensity (d : ℕ) : ℝ := 1/2-outerColumnRate d^2/2

theorem quadraticOutputDensity_lower {d : ℕ} (hd : 3 ≤ d) :
    (9/32 : ℝ) < quadraticOutputDensity d := by
  unfold quadraticOutputDensity
  by_cases hd8 : d ≤ 8
  · linarith [small_deletion_capacity hd hd8]
  · have hp := (outerColumnRate_bounds hd).1
    have hl := outerColumnRate_small (show 9 ≤ d by omega)
    have hsq : outerColumnRate d^2 < (1/75 : ℝ)^2 :=
      (sq_lt_sq₀ hp.le (by norm_num)).mpr hl
    norm_num at hsq
    linarith

theorem quadraticOutputDimension_limit {d : ℕ} (hd : 3 ≤ d) :
    Tendsto (fun h : ℕ => (quadraticOutputDimension d h : ℝ)/(h : ℝ)^2) atTop
      (𝓝 (quadraticOutputDensity d)) := by
  have hN : Tendsto (fun h : ℕ => ((h+1).choose 2 : ℝ)/(h : ℝ)^2) atTop (𝓝 (1/2 : ℝ)) := by
    simpa [show ∀ h : ℕ, h+2-1=h+1 by omega, Nat.factorial] using monomial_count_normalized_tendsto 2
  have hrq : Tendsto (fun h : ℕ => (((h+1).choose 2 : ℝ)-(deletedTargetCount d h : ℝ))/(h : ℝ)^2)
      atTop (𝓝 (quadraticOutputDensity d)) := by
    simpa only [sub_div,quadraticOutputDensity] using hN.sub (deletedTargetCount_limit hd)
  have hc : 0 < quadraticOutputDensity d := lt_trans (by norm_num) (quadraticOutputDensity_lower hd)
  have hg : Tendsto (fun h : ℕ => ((0 : ℕ) : ℝ)/(h : ℝ)^2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.cast_zero,zero_div] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  simpa only [quadraticOutputDimension,Nat.sub_zero] using
    (natural_budget_limit (fun h => (h+1).choose 2) (deletedTargetCount d) (fun _ => 0)
      (by omega : 0 < 2) (quadraticOutputDensity d) hc hrq hg).2

theorem upperCount_fits_quadraticOutputDimension {d : ℕ} (hd : 3 ≤ d) :
    ∀ᶠ h : ℕ in atTop, upperCount h 2 ≤ quadraticOutputDimension d h := by
  have hρ := quadratic_critical_ratio_lt
  have hδ := quadraticOutputDensity_lower hd
  have hgap : criticalRatio 2/((2 : ℕ).factorial : ℝ) < quadraticOutputDensity d := by
    norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,mul_one]
    linarith
  filter_upwards [eventually_lt_of_normalized_limits _ _ 2 _ _
    (upperCount_normalized_limit (by omega)) (quadraticOutputDimension_limit hd) hgap] with h hh
  exact_mod_cast hh.le

end Froberg
