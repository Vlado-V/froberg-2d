module

public import Froberg.UniformTargetConvolution

@[expose] public section

/-! Uniform low quadratic target witnesses with an eventual quadratic base. -/
noncomputable section
namespace Froberg
open Filter Module
open scoped Topology
universe u

theorem eventually_quadratic_row_three_uniform {d : ℕ} (hd : 3 ≤ d)
    (D : ℕ → ℕ) (δ : ℝ) (hδ : (1/6 : ℝ) < δ)
    (hDlim : Tendsto (fun n : ℕ => (D n : ℝ)/(n : ℝ)^2) atTop (𝓝 δ))
    (hDupper : ∀ᶠ n : ℕ in atTop, D n ≤ (n+1).choose 2) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop, ∀ (K : Type u) [Field K] [Infinite K],
      ∃ (W : Submodule K (Forms K h 2))
        (o : Fin ⌈countAlpha d*(h : ℝ)^2*(m : ℝ)^(d-2)⌉₊ → W)
        (f : Fin ⌈countAlpha d*(h : ℝ)^2*(m : ℝ)^(d-2)⌉₊ → Forms K m (d-2)),
        finrank K W = D h ∧
        Function.Surjective (biformFamilyMap (x := 1) (y := d-1) (fun i => (o i).val) f) := by
  apply eventually_extended_middle_biform_uniform (by omega) (by omega) (by omega)
    (countAlpha d) δ ?_ ?_ D hDlim ?_
  · rw [convolutionOutputThreshold_row_three hd]
    exact (quadratic_target_costs_lt_alpha hd).2.1
  · norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,
      mul_one]
    exact hδ
  · simpa only [show ∀ n : ℕ, n+2-1=n+1 by omega] using hDupper

theorem eventually_quadratic_row_four_of_endpoint_uniform {d : ℕ} (hd : 3 ≤ d)
    (N₂ : ℕ)
    (hquad : ∀ n, N₂ ≤ n → ∀ (K : Type u) [Field K] [Infinite K],
      GenericEndpoint K n 2 (upperCount n 2))
    (D : ℕ → ℕ)
    (hD : ∀ᶠ h : ℕ in atTop, upperCount h 2 ≤ D h ∧ D h ≤ (h+1).choose 2) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop, ∀ (K : Type u) [Field K] [Infinite K],
      ∃ (W : Submodule K (Forms K h 2))
        (o : Fin ⌈countAlpha d*(h : ℝ)^2*(m : ℝ)^(d-2)⌉₊ → W)
        (f : Fin ⌈countAlpha d*(h : ℝ)^2*(m : ℝ)^(d-2)⌉₊ → Forms K m (d-2)),
        finrank K W = D h ∧
        Function.Surjective (biformFamilyMap (x := 2) (y := d-2) (fun i => (o i).val) f) := by
  have hgap : (criticalRatio 2/((2 : ℕ).factorial : ℝ)) /
      (((d-2+1+(d-2)-1).choose (d-2) : ℝ)*((d-2).factorial : ℝ)) < countAlpha d := by
    have h := (quadratic_target_costs_lt_alpha hd).2.2
    rw [show d-2+1+(d-2)-1=2*d-4 by omega]
    norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,
      mul_one]
    convert h using 1
    unfold countTauFour
    ring
  have hcount := convolution_blocks_eventually_fit_density (j := 2) (a := d-2+1)
    (e := d-2) (by omega) (by omega) (by omega) (fun n => upperCount n 2)
    (criticalRatio 2/((2 : ℕ).factorial : ℝ)) (countAlpha d) (upperCount_normalized_limit (by omega)) hgap
  filter_upwards [hcount,hD,eventually_gt_atTop (0 : ℕ),eventually_ge_atTop N₂] with h hc hD hh hN
  filter_upwards [hc,eventually_gt_atTop (0 : ℕ)] with m hm hm0
  intro K _ _
  obtain ⟨Q,_,hQ⟩ := exists_prefix_surjective_at_upperCount hh (hquad h hN K)
  exact exists_biform_family_in_extended_output_space hh hm0 Q hQ hD.1
    (by simpa only [show h+2-1=h+1 by omega] using hD.2) hm

theorem eventually_quadratic_row_three_exact_uniform {d : ℕ} (hd : 3 ≤ d) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop, ∀ (K : Type u) [Field K] [Infinite K], ∀ r : ℕ,
      countAlpha d*(h : ℝ)^2*(m : ℝ)^(d-2) ≤ (r : ℝ) →
      QuadraticTargetWitness K d h m r 1 (d-1) := by
  have hδ : (1/6 : ℝ) < quadraticOutputDensity d :=
    lt_trans (by norm_num) (quadraticOutputDensity_lower hd)
  have he := eventually_quadratic_row_three_uniform hd (quadraticOutputDimension d)
    (quadraticOutputDensity d) hδ (quadraticOutputDimension_limit hd)
    (Eventually.of_forall fun h => Nat.sub_le _ _)
  filter_upwards [he] with h hh
  filter_upwards [hh] with m hm
  intro K _ _ r hr
  obtain ⟨W,o,f,hW,hs⟩ := hm K
  obtain ⟨O,F,hF⟩ := biformFamily_surjective_extend_subspace W o f (Nat.ceil_le.mpr hr) hs
  exact ⟨W,O,F,hW,hF⟩

theorem eventually_quadratic_row_four_exact_of_endpoint_uniform {d : ℕ} (hd : 3 ≤ d)
    (N₂ : ℕ)
    (hquad : ∀ h, N₂ ≤ h → ∀ (K : Type u) [Field K] [Infinite K],
      GenericEndpoint K h 2 (upperCount h 2)) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop, ∀ (K : Type u) [Field K] [Infinite K], ∀ r : ℕ,
      countAlpha d*(h : ℝ)^2*(m : ℝ)^(d-2) ≤ (r : ℝ) →
      QuadraticTargetWitness K d h m r 2 (d-2) := by
  have hD : ∀ᶠ h : ℕ in atTop, upperCount h 2 ≤ quadraticOutputDimension d h ∧
      quadraticOutputDimension d h ≤ (h+1).choose 2 := by
    filter_upwards [upperCount_fits_quadraticOutputDimension hd] with h hh
    exact ⟨hh,Nat.sub_le _ _⟩
  have he := eventually_quadratic_row_four_of_endpoint_uniform hd N₂ hquad (quadraticOutputDimension d) hD
  filter_upwards [he] with h hh
  filter_upwards [hh] with m hm
  intro K _ _ r hr
  obtain ⟨W,o,f,hW,hs⟩ := hm K
  obtain ⟨O,F,hF⟩ := biformFamily_surjective_extend_subspace W o f (Nat.ceil_le.mpr hr) hs
  exact ⟨W,O,F,hW,hF⟩

end Froberg
