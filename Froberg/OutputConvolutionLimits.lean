module

public import Froberg.ConvolutionBlockLimits
public import Froberg.PrefixConvolution

@[expose] public section

/-! Convolution applied to output counts with a known leading coefficient. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem convolution_blocks_eventually_fit_density {j a e : ℕ} (hj : 0 < j)
    (ha : 0 < a) (he : 0 < e) (q : ℕ → ℕ) (c α : ℝ)
    (hq : Tendsto (fun n : ℕ => (q n : ℝ)/(n : ℝ)^j) atTop (𝓝 c))
    (hgap : c/(((a+e-1).choose e : ℝ)*(e.factorial : ℝ)) < α) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      convolutionBlockCount (q h) a e*(m+a+e-2).choose e ≤
        ⌈α*(h : ℝ)^j*(m : ℝ)^e⌉₊ := by
  have hl := (convolutionBlockCount_normalized_limit (e := e) hj ha q c hq).div_const
    (e.factorial : ℝ)
  have hgap' : (c/((a+e-1).choose e : ℝ))/(e.factorial : ℝ) < α := by
    simpa only [div_div] using hgap
  filter_upwards [hl.eventually (gt_mem_nhds hgap'),eventually_gt_atTop (0 : ℕ)] with h hh hh0
  have hp : (0 : ℝ)<(h : ℝ)^j := pow_pos (by exact_mod_cast hh0) _
  have heq : ((convolutionBlockCount (q h) a e : ℝ)/(h : ℝ)^j)/(e.factorial : ℝ) =
      ((convolutionBlockCount (q h) a e : ℝ)/(e.factorial : ℝ))/(h : ℝ)^j := by ring
  rw [heq] at hh
  exact convolutionGeneratorCount_eventually_fits he ha (α*(h : ℝ)^j) ((div_lt_iff₀ hp).mp hh)

variable {K : Type*} [Field K] [Infinite K]

theorem eventually_biform_surjective_of_output_count {j x e y : ℕ}
    (hj : 0 < j) (he : 0 < e) (q : ℕ → ℕ) (c α : ℝ)
    (hq : Tendsto (fun n : ℕ => (q n : ℝ)/(n : ℝ)^j) atTop (𝓝 c))
    (hgap : c/(((y+1+e-1).choose e : ℝ)*(e.factorial : ℝ)) < α)
    (houtput : ∀ᶠ h : ℕ in atTop, ∃ Q : Fin (q h) → Forms K h j,
      Function.Surjective (prefixMultiplication Q x)) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      ∃ (o : Fin ⌈α*(h : ℝ)^j*(m : ℝ)^e⌉₊ → Forms K h j)
        (f : Fin ⌈α*(h : ℝ)^j*(m : ℝ)^e⌉₊ → Forms K m e),
        Function.Surjective (biformFamilyMap (x := x) (y := y) o f) := by
  filter_upwards [convolution_blocks_eventually_fit_density hj (show 0 < y+1 by omega)
    he q c α hq hgap,houtput] with h hcount hQ
  obtain ⟨Q,hQ⟩ := hQ
  filter_upwards [hcount,eventually_gt_atTop (0 : ℕ)] with m hm hm0
  obtain ⟨o,f,_,hsurj⟩ := exists_biform_family_of_prefix (y := y) hm0 Q hQ hm
  exact ⟨o,f,hsurj⟩

end Froberg
