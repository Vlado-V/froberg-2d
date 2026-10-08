import Froberg.RoundingLimits
import Froberg.CapacityReserve
import Froberg.AsymptoticCounts

/-! The exact floor count used to augment the scalar family. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem floor_normalized_limit (f : ℕ → ℝ) {k : ℕ} (hk : 0<k) (c : ℝ)
    (hf : ∀ᶠ n : ℕ in atTop,0≤f n)
    (hlim : Tendsto (fun n => f n/(n : ℝ)^k) atTop (𝓝 c)) :
    Tendsto (fun n => (⌊f n⌋₊ : ℝ)/(n : ℝ)^k) atTop (𝓝 c) := by
  have hlo : ∀ᶠ n : ℕ in atTop,(0 : ℝ)≤f n-(⌊f n⌋₊ : ℝ) :=
    hf.mono fun n hn => sub_nonneg.mpr (Nat.floor_le hn)
  have hhi : ∀ᶠ n : ℕ in atTop,f n-(⌊f n⌋₊ : ℝ)≤1 :=
    Eventually.of_forall fun n => by linarith [Nat.lt_floor_add_one (f n)]
  have he := tendsto_bdd_div_atTop_nhds_zero hlo hhi (nat_power_tendsto_atTop k hk)
  simpa only [sub_zero,sub_div,sub_sub_cancel] using hlim.sub he

def scalarReserveCount (d m : ℕ) : ℕ := ⌊scalarReserveDensity d*(m : ℝ)^d⌋₊

theorem scalarReserveCount_limit {d : ℕ} (hd : 0<d) :
    Tendsto (fun m : ℕ => (scalarReserveCount d m : ℝ)/(m : ℝ)^d)
      atTop (𝓝 (scalarReserveDensity d)) := by
  apply floor_normalized_limit _ hd _ (Eventually.of_forall fun m => by
    exact mul_nonneg (scalarReserveDensity_pos d).le (by positivity))
  exact scaled_power_normalized_limit _ _

end Froberg
