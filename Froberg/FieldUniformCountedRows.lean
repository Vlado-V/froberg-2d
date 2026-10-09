module

public import Froberg.ScalarVectorRowsOpen
public import Froberg.VectorModelCoordinates
public import Froberg.FieldUniformCountedPrivate
public import Froberg.FieldUniformC4Growth

@[expose] public section

/-! The exact reserve absorbs every lower-order scalar overhead and any
fixed private family in the common first and higher odd-row construction. -/
noncomputable section
namespace Froberg
open Filter Module MvPolynomial Quartic VectorMultiplicationCoordinates
open scoped Topology

theorem uniform_exact_counts_scalar_vector_rows_open {d k h lo b : ℕ}
    (hd : 3≤d) (hk : 0<k) (hh : h=k*centralHalfBinomial d) (hhpos : 0<h)
    (upper : Bool) (a f e extra : ℕ → ℕ) (ha : ∀ n,a n≤n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0<δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n))
    (hextra : Tendsto (fun n : ℕ => (extra n : ℝ)/(n : ℝ)^(d-1)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,∀ (K : Type) [Field K] [Infinite K],
      ∃ P : MvPolynomial (Fin (finrank K
        (ScalarVectorParameters K h n d (f n+b) (upperCount n d+extra n)))) K,
        (∃ p : ScalarVectorParameters K h n d (f n+b) (upperCount n d+extra n),
          eval ((Module.finBasis K _).equivFun p) P≠0) ∧
        ∀ p : ScalarVectorParameters K h n d (f n+b) (upperCount n d+extra n),
          eval ((Module.finBasis K _).equivFun p) P≠0 →
          FirstVectorRowExact p.2 p.1 ∧ HigherOddRows p.2 p.1 := by
  have he : Tendsto (fun n : ℕ => (extra n : ℝ)/(n : ℝ)^d) atTop (𝓝 0) := by
    have ht := hextra.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [div_div,←pow_succ,show d-1+1=d by omega] using ht
  have hS : Tendsto (fun n : ℕ => ((upperCount n d+extra n : ℕ) : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ))) := by
    simpa only [Nat.cast_add,add_div,add_zero] using (upperCount_normalized_limit (by omega : 2≤d)).add he
  have hfixed : Tendsto (fun n : ℕ => (b : ℝ)/(n : ℝ)^(d-1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (nat_power_tendsto_atTop (d-1) (by omega))
  have hF : Tendsto (fun n : ℕ => ((f n+b : ℕ) : ℝ)/(n : ℝ)^(d-1)) atTop
      (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))) := by
    simpa only [Nat.cast_add,add_div,add_zero] using
      (exact_conditions_outer_limit hd upper a f e hc).add hfixed
  have hscalar := eventually_uniform_odd_scalar_layers_open hd hhpos
    (fun n => upperCount n d+extra n) (fun n => f n+b) hS hF
  have hupper := eventually_upper_odd_row_budget hd hhpos (fun n => f n+b) hF
  have hcapacity := VectorExpansionOpen.eventually_field_uniform_augmented_outer_capacity (b := b)
    hd f extra hδ hextra hreserve
  obtain ⟨G,hG,hmodels⟩ := uniform_exact_counts_private_strict_open (b := b)
    hd hk hh upper a f e ha hc
  filter_upwards [hscalar,hupper,hcapacity,hmodels,eventually_gt_atTop (0 : ℕ)]
    with n hsn hun hcn hmn hn
  intro K _ _
  obtain ⟨D,hD,hmodel⟩ := hmn K
  obtain ⟨E,hE,hEmodel⟩ := VectorParameters.principal_open_in_finite_coordinates D hD
    (fun g => VectorExpansionOpen.StrictModel g d (G*(n : ℝ)^d) ∧
      (upperCount n d+extra n)*finrank K (VectorExpansionOpen.Source g)≤
        finrank K (VectorExpansionOpen.Target g d))
    (fun p hp => ⟨hmodel p hp,hcn K _ _ (hmodel p hp)⟩)
  exact scalar_vector_rows_open hhpos hn (by omega) E hE hEmodel (hsn K) hun

end Froberg
