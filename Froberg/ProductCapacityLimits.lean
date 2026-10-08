import Froberg.PairedCapacity
import Froberg.CapacityProduct

/-! The exact finite product capacities converge to the B.9 coefficients.
Both the output subtraction and the scalar division are natural operations. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem nat_sub_normalized_limit (F G : ℕ → ℕ) {k : ℕ} (hk : 0 < k)
    (a b : ℝ) (hF : Tendsto (fun n : ℕ => (F n : ℝ)/(n : ℝ)^k) atTop (𝓝 a))
    (hG : Tendsto (fun n : ℕ => (G n : ℝ)/(n : ℝ)^k) atTop (𝓝 b)) (hba : b < a) :
    Tendsto (fun n : ℕ => ((F n-G n : ℕ) : ℝ)/(n : ℝ)^k) atTop (𝓝 (a-b)) := by
  have hrq : Tendsto (fun n : ℕ => ((F n : ℝ)-(G n : ℝ))/(n : ℝ)^k)
      atTop (𝓝 (a-b)) := by simpa only [sub_div] using hF.sub hG
  have hz : Tendsto (fun n : ℕ => ((0 : ℕ) : ℝ)/(n : ℝ)^k) atTop (𝓝 (0 : ℝ)) := by simp
  simpa only [Nat.sub_zero] using
    (natural_budget_limit F G (fun _ => 0) hk (a-b) (sub_pos.mpr hba) hrq hz).2

theorem deletedTargetCount_higher_limit {d j : ℕ} (hd : 3 ≤ d) (hj : 2 < j) :
    Tendsto (fun n : ℕ => (deletedTargetCount d n : ℝ)/(n : ℝ)^j) atTop (𝓝 (0 : ℝ)) := by
  have hl := (deletedTargetCount_limit hd).div_atTop
    (nat_power_tendsto_atTop (j-2) (by omega))
  apply hl.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [div_div,← pow_add,show 2+(j-2)=j by omega]

def diagonalOutputCount (d j h : ℕ) : ℕ := (h/2).choose j-deletedTargetCount d h

def diagonalOutputDensity (d j : ℕ) : ℝ :=
  (1/2 : ℝ)^j/(j.factorial : ℝ) - if j=2 then outerColumnRate d^2/2 else 0

theorem diagonalOutputDensity_pos {d j : ℕ} (hd : 9 ≤ d) (hj : 2 ≤ j) :
    0 < diagonalOutputDensity d j := by
  unfold diagonalOutputDensity
  by_cases hj2 : j=2
  · subst j
    rw [if_pos rfl]
    have hp := (outerColumnRate_bounds (show 3 ≤ d by omega)).1
    have hl := outerColumnRate_small hd
    have hs : outerColumnRate d^2 < (1/75 : ℝ)^2 := (sq_lt_sq₀ hp.le (by norm_num)).mpr hl
    norm_num [Nat.factorial] at hs ⊢
    linarith
  · rw [if_neg hj2,sub_zero]
    positivity

theorem diagonalOutputCount_limit {d j : ℕ} (hd : 9 ≤ d) (hj : 2 ≤ j) :
    Tendsto (fun n : ℕ => (diagonalOutputCount d j n : ℝ)/(n : ℝ)^j) atTop
      (𝓝 (diagonalOutputDensity d j)) := by
  have hG : Tendsto (fun n : ℕ => (deletedTargetCount d n : ℝ)/(n : ℝ)^j) atTop
      (𝓝 (if j=2 then outerColumnRate d^2/2 else 0)) := by
    by_cases hj2 : j=2
    · subst j
      simpa using deletedTargetCount_limit (show 3 ≤ d by omega)
    · simpa only [if_neg hj2] using deletedTargetCount_higher_limit (show 3 ≤ d by omega) (by omega : 2 < j)
  apply nat_sub_normalized_limit _ _ (by omega) _ _ (half_index_choose_limit j) hG
  have h := diagonalOutputDensity_pos hd hj
  exact sub_pos.mp h

/-- A strict B.9 leading gap gives the exact rounded diagonal capacity. -/
theorem eventually_diagonal_capacity_of_density {d j e : ℕ}
    (hd : 9 ≤ d) (hj : 2 ≤ j) (he : 0 < e) (γ : ℝ) (hγ : 0 ≤ γ)
    (hgap : γ < diagonalOutputDensity d j/(2^(e+1)*(e.factorial : ℝ))) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      ⌈γ*(h : ℝ)^j*(m : ℝ)^e⌉₊ ≤ diagonalOutputCount d j h*((m/2).choose e/2) := by
  have hl := (diagonalOutputCount_limit hd hj).div_const (2^(e+1)*(e.factorial : ℝ))
  filter_upwards [hl.eventually (lt_mem_nhds hgap),eventually_gt_atTop (0 : ℕ)] with h hh hh0
  have hp : (0 : ℝ) < (h : ℝ)^j := pow_pos (by exact_mod_cast hh0) _
  have heq : ((diagonalOutputCount d j h : ℝ)/(h : ℝ)^j)/(2^(e+1)*(e.factorial : ℝ)) =
      ((diagonalOutputCount d j h : ℝ)/(2^(e+1)*(e.factorial : ℝ)))/(h : ℝ)^j := by ring
  rw [heq] at hh
  apply eventually_paired_capacity he (fun m => ⌈γ*(h : ℝ)^j*(m : ℝ)^e⌉₊) (γ*(h : ℝ)^j)
  · exact ceil_normalized_limit _ he _ (Eventually.of_forall fun m => by positivity)
      (scaled_power_normalized_limit _ _)
  · exact (lt_div_iff₀ hp).mp hh

end Froberg
