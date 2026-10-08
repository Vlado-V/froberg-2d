import Froberg.PrefixConvolution
import Froberg.PrefixOutputLimits
import Froberg.TargetCosts

/-! Actual middle-row witnesses at every density strictly above the B.7 threshold. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology
variable {K : Type*} [Field K] [Infinite K]

def convolutionOutputThreshold (j x e y : ℕ) : ℝ :=
  ((x.factorial : ℝ)/((j+x).factorial : ℝ)) /
    (((y+1+e-1).choose e : ℝ)*(e.factorial : ℝ))

/-- First choose a sufficiently large outer dimension, then sufficiently many
scalar variables. The resulting generators are actual homogeneous biforms. -/
theorem eventually_middle_biform_surjective {j x e y : ℕ} (hj : 0 < j)
    (hxj : x < j) (he : 0 < e) (α : ℝ)
    (hα : convolutionOutputThreshold j x e y < α) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      ∃ (o : Fin ⌈α*(h : ℝ)^j*(m : ℝ)^e⌉₊ → Forms K h j)
        (f : Fin ⌈α*(h : ℝ)^j*(m : ℝ)^e⌉₊ → Forms K m e),
        Function.Surjective (biformFamilyMap (x := x) (y := y) o f) := by
  have hQ : 0 < (y+1+e-1).choose e := Nat.choose_pos (by omega)
  have hden : (0 : ℝ)<((y+1+e-1).choose e : ℝ)*(e.factorial : ℝ) := by positivity
  have hbetween : (x.factorial : ℝ)/((j+x).factorial : ℝ) <
      α*(((y+1+e-1).choose e : ℝ)*(e.factorial : ℝ)) :=
    (div_lt_iff₀ hden).mp hα
  obtain ⟨τ,hτlo,hτhi⟩ := exists_between hbetween
  have hτ : 0 < τ := lt_trans (by positivity) hτlo
  have hgap : τ/(((y+1+e-1).choose e : ℝ)*(e.factorial : ℝ)) < α :=
    (div_lt_iff₀ hden).mpr hτhi
  filter_upwards [rounded_prefix_output_count hj τ hτlo,
    rounded_convolution_blocks_margin hj (show 0 < y+1 by omega) τ α hτ hgap,
    eventually_ge_atTop ((x+j).choose x*((x+j).choose x*j.choose x)),
    eventually_gt_atTop (0 : ℕ)] with h houtput hblocks hlarge hh
  filter_upwards [convolutionGeneratorCount_eventually_fits he (show 0 < y+1 by omega)
    (α*(h : ℝ)^j) hblocks, eventually_gt_atTop (0 : ℕ)] with m hgen hm
  exact exists_biform_family_of_prefix_counts (K := K) hh hm hxj hlarge houtput hgen

/-- The factorial threshold in the manuscript is exactly the threshold of the
actual finite convolution construction. -/
theorem convolutionOutputThreshold_targetCost {d j b : ℕ}
    (hjd : j≤d) (hjb : j≤b) (hbd : b≤d+j) :
    convolutionOutputThreshold j (b-j) (d-j) (d+j-b) = targetCost d j b := by
  rw [targetCost_eq_convolution hjd hbd]
  unfold convolutionOutputThreshold
  rw [show j+(b-j)=b by omega,
    show d+j-b+1+(d-j)-1=2*d-b by omega]
  rw [mul_comm ((2*d-b).choose (d-j) : ℝ)]

/-- Every strict-prefix middle row has an actual biform surjection at the
prescribed asymptotic density. -/
theorem eventually_target_row_from_prefix {d j b : ℕ} (hj : 0 < j) (hjd : j < d)
    (hjb : j≤b) (hbj : b<2*j) (hbd : b≤d+j) (α : ℝ) (hα : targetCost d j b < α) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      ∃ (o : Fin ⌈α*(h : ℝ)^j*(m : ℝ)^(d-j)⌉₊ → Forms K h j)
        (f : Fin ⌈α*(h : ℝ)^j*(m : ℝ)^(d-j)⌉₊ → Forms K m (d-j)),
        Function.Surjective (biformFamilyMap (x := b-j) (y := d+j-b) o f) := by
  apply eventually_middle_biform_surjective hj (by omega) (by omega) α
  rwa [convolutionOutputThreshold_targetCost hjd.le hjb hbd]

end Froberg
