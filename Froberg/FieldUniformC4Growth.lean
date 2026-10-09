module

public import Froberg.CountedBaseC4Growth

@[expose] public section

/-! Field-independent cutoffs for the scalar growth estimates used in C.4.
The only asymptotic steps below concern natural counts and real inequalities;
the field and the projected output map are chosen after those cutoffs. -/
noncomputable section
namespace Froberg
open Filter Module Quartic
open scoped Topology

/-- Every non-top layer has a common growth open, with one cutoff for all
infinite fields. The auxiliary scalar count is not added to the generators. -/
theorem eventually_uniform_odd_scalar_layers_open {h d : ℕ}
    (hd : 3 ≤ d) (hh : 0 < h) (qS qO : ℕ → ℕ)
    (hS : Tendsto (fun n : ℕ => (qS n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ))))
    (hO : Tendsto (fun n : ℕ => (qO n : ℝ)/(n : ℝ)^(d-1)) atTop
      (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ)))) :
    ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K],
      HasOddScalarLayersOpen K h n d (qO n) (qS n) (scalarReserveCount d n) := by
  let I := {b : Fin (d+1) // 3 ≤ b.val}
  have hall : ∀ᶠ n : ℕ in atTop, ∀ b : I,
      OddLayerCount h n d (qS n) (qO n)
        ⌊oddRowExtraDensity d*(n : ℝ)^d⌋₊ b.val.val := by
    apply Filter.eventually_all.mpr
    intro b
    exact eventually_augmented_higher_odd_row_budget hd b.property
      (by have := b.val.isLt; omega) hh qS qO hS hO
  filter_upwards [hall,eventually_gt_atTop (0 : ℕ)] with n hn hn0
  intro K _ _
  apply odd_scalar_layers_open hh hn0
  intro b hb hbd
  exact hn ⟨⟨b,by omega⟩,hb⟩

/-- The top growth cutoff is uniform both in the field and in the projection. -/
theorem eventually_uniform_projected_top_growth_open {h e b : ℕ}
    (hh : 0 < h) (he : 2 ≤ e) (hb : 0 < b)
    (hratio : (h : ℝ)/(2*((1+e : ℕ) : ℝ)) ≤
      (b : ℝ)/((h+e-1).choose e : ℝ))
    (qF qS : ℕ → ℕ)
    (hF : Tendsto (fun m : ℕ => (qF m : ℝ)/(m : ℝ)^e) atTop
      (𝓝 ((h : ℝ)*criticalRatio (1+e)/(e.factorial : ℝ))))
    (hS : Tendsto (fun m : ℕ => (qS m : ℝ)/(m : ℝ)^(1+e)) atTop
      (𝓝 (criticalRatio (1+e)/((1+e).factorial : ℝ)))) :
    ∀ᶠ m : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K],
      ∀ P : Forms K h (1+e) →ₗ[K] (Fin b → K),
      (∀ L : Submodule K (Forms K h e), b*finrank K L ≤
        finrank K (Forms K h e)*
          finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := e)) L).map P)) →
      ProjectedTopGrowthOpen P m (qF m) (qS m) (scalarReserveCount (1+e) m) := by
  have hbudget := eventually_augmented_top_budget (show 3 ≤ 1+e by omega)
    (Nat.choose_pos (show e ≤ h+e-1 by omega)) hb hratio qF qS
    (by simpa only [show 1+e-1=e by omega] using hF) hS
  filter_upwards [hbudget,eventually_gt_atTop (0 : ℕ)] with m hm hmpos
  intro K _ _ P hP
  exact projected_top_growth_open hh hmpos hb P hP hm

/-- Exact count sequences give the common non-top open uniformly in the field. -/
theorem eventually_uniform_counted_odd_scalar_growth {h d k lo : ℕ}
    (hd : 3 ≤ d) (hh : 0 < h) (upper : Bool) (a f e : ℕ → ℕ)
    (hc : ∀ᶠ n in atTop, ExactCountConditions d k h lo n (a n) (f n) (e n) upper) :
    ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K],
      HasOddScalarLayersOpen K h n d (f n) (upperCount n d) (scalarReserveCount d n) := by
  apply eventually_uniform_odd_scalar_layers_open hd hh (fun n => upperCount n d) f
  · exact upperCount_normalized_limit (by omega)
  · exact exact_conditions_outer_limit hd upper a f e hc

/-- All base C.4 growth conditions have a common field-independent cutoff.
Only the resulting principal polynomial and its point depend on the field. -/
theorem eventually_uniform_counted_base_c4_growth {h d b k lo : ℕ}
    (hd : 3 ≤ d) (hh : 0 < h) (hb : 0 < b)
    (hratio : (h : ℝ)/(2*((1+(d-1) : ℕ) : ℝ)) ≤
      (b : ℝ)/((h+(d-1)-1).choose (d-1) : ℝ))
    (upper : Bool) (a f e : ℕ → ℕ)
    (hc : ∀ᶠ n in atTop, ExactCountConditions d k h lo n (a n) (f n) (e n) upper) :
    ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K],
      ∀ R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K),
      (∀ L : Submodule K (Forms K h (d-1)), b*finrank K L ≤
        finrank K (Forms K h (d-1))*
          finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := d-1)) L).map R)) →
      HasBaseC4GrowthOpen (m := n) (f := f n) (q := upperCount n d)
        (by omega : 1 ≤ d) R (scalarReserveCount d n) := by
  have hd' : 1+(d-1)=d := by omega
  have hF := exact_conditions_outer_limit hd upper a f e hc
  have ht := eventually_uniform_projected_top_growth_open hh (show 2 ≤ d-1 by omega)
    hb hratio f (fun n => upperCount n d)
    (by simpa only [hd'] using hF)
    (by simpa only [hd'] using upperCount_normalized_limit (d := d) (by omega))
  have hm := eventually_uniform_counted_odd_scalar_growth hd hh upper a f e hc
  simp only [hd'] at ht
  filter_upwards [ht,hm] with n htop hmid
  intro K _ _ R hR
  exact has_base_c4_growth_open (by omega : 1 ≤ d) R (htop K R hR) (hmid K)

end Froberg
