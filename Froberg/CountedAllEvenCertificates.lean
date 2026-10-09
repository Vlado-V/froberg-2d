module

public import Froberg.PreparedCountedOddCycles
public import Froberg.PreparedCountedIndependence
public import Froberg.PreparedAllEvenCounts

@[expose] public section

/-! The actual all-even family, including finitely many temporary columns,
has a uniform odd-exactness open. Output constraints may be chosen after
the scalar threshold. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg.PreparedTarget
open Froberg Filter Module MvPolynomial Quartic VectorMultiplicationCoordinates
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

theorem exact_counts_all_even_odd_open {d k h lo u : ℕ}
    (hd : 3≤d) (hdodd : d%2=1) (hk : 0<k)
    (hh : h=k*centralHalfBinomial d) (hhpos : 0<h)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n,a n≤n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0<δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n))
    (extraSlots : ℕ) :
    ∀ᶠ n : ℕ in atTop,∀ (O : ℕ → Submodule K (Poly K h))
      (hO : ∀ j∈PreparedParameters.allEvenIndices d,O j≤Forms K h j),
      HasOddCyclesOpen (m := n) (d := d) (q := upperCount n d)
        (f := f n) (u := u) (counts := PreparedParameters.allEvenCount d h n (e n+extraSlots)) hO := by
  let extra := fun n => e n+(∑ j∈activeHigherIndices d,higherGeneratorCount d h n j)+extraSlots
  let qS := fun n => Fintype.card (PreparedParameters.Label (upperCount n d)
    (PreparedParameters.allEvenIndices d) (PreparedParameters.allEvenCount d h n (e n+extraSlots)))
  have he := hc.mono fun n hn => hn.quadratic_upper
  have hextra := prepared_extra_scalar_count_lower_order hd h extraSlots e he
  have hcount (n : ℕ) : upperCount n d+extra n=qS n := by
    rw [show qS n=Fintype.card (PreparedParameters.Label (upperCount n d)
      (PreparedParameters.allEvenIndices d) (PreparedParameters.allEvenCount d h n (e n+extraSlots))) from rfl,
      PreparedParameters.allEvenLabel_card hd,preparedLabel_card,sum_targetLayerCount hd]
    dsimp only [extra]
    omega
  have hS : Tendsto (fun n : ℕ => (qS n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ))) :=
    PreparedParameters.allEvenLabel_count_limit hd h extraSlots e he
  have hfixed : Tendsto (fun n : ℕ => (u : ℝ)/(n : ℝ)^(d-1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (nat_power_tendsto_atTop (d-1) (by omega))
  have hF : Tendsto (fun n : ℕ => ((f n+u : ℕ) : ℝ)/(n : ℝ)^(d-1)) atTop
      (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))) := by
    simpa only [Nat.cast_add,add_div,add_zero] using
      (exact_conditions_outer_limit hd upper a f e hc).add hfixed
  have hscalar := eventually_odd_scalar_layers_open (K := K) hd hhpos qS (fun n => f n+u) hS hF
  have hupper := eventually_upper_odd_row_budget hd hhpos (fun n => f n+u) hF
  have hcapacity := VectorExpansionOpen.eventually_augmented_outer_capacity (K := K) (b := u)
    hd f extra hδ hextra hreserve
  obtain ⟨G,hG,hmodels⟩ := exact_counts_private_strict_open (K := K) (b := u)
    hd hk hh upper a f e ha hc
  filter_upwards [hscalar,hupper,hcapacity,hmodels,eventually_gt_atTop (0 : ℕ)]
    with n hsn hun hcn hmn hn
  intro O hO
  obtain ⟨D,hD,hmodel⟩ := hmn
  obtain ⟨E,hE,hEmodel⟩ := VectorParameters.principal_open_in_finite_coordinates D hD
    (fun g => VectorExpansionOpen.StrictModel g d (G*(n : ℝ)^d) ∧
      Fintype.card (PreparedParameters.Label (upperCount n d) (PreparedParameters.allEvenIndices d)
        (PreparedParameters.allEvenCount d h n (e n+extraSlots)))*finrank K (VectorExpansionOpen.Source g)≤
          finrank K (VectorExpansionOpen.Target g d)) (by
      intro p hp
      refine ⟨hmodel p hp,?_⟩
      have hh := hcn (G*(n : ℝ)^d) (VectorParameters.generators p) (hmodel p hp)
      rwa [hcount] at hh)
  apply prepared_odd_cycles_open hhpos hn hd hdodd hO
    (fun j hj => (PreparedParameters.mem_allEvenIndices.mp hj).2.1)
    (fun j hj => by have := (PreparedParameters.mem_allEvenIndices.mp hj).1; omega)
    (fun j hj => (PreparedParameters.mem_allEvenIndices.mp hj).2.2) E hE hEmodel
  · exact hsn
  · exact hun

theorem exact_counts_all_even_independent_open {d k h lo u : ℕ}
    (hd : 3≤d) (hh : 0<h) (upper : Bool) (a f e : ℕ → ℕ)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    (extraSlots : ℕ) :
    ∀ᶠ n : ℕ in atTop,∀ (O : ℕ → Submodule K (Poly K h))
      (hO : ∀ j∈PreparedParameters.allEvenIndices d,O j≤Forms K h j),
      HasIndependentOpen (m := n) (q := upperCount n d) (f := f n) (u := u)
        (counts := PreparedParameters.allEvenCount d h n (e n+extraSlots)) (by omega : 0<d) hO
        (fun j hj => (PreparedParameters.mem_allEvenIndices.mp hj).2.1) := by
  have hρ := (criticalRatio_bounds (show 2≤d by omega)).2.1
  have he := hc.mono fun n hn => hn.quadratic_upper
  have hS := PreparedParameters.allEvenLabel_count_limit hd h extraSlots e he
  have hfixed : Tendsto (fun n : ℕ => (u : ℝ)/(n : ℝ)^(d-1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (nat_power_tendsto_atTop (d-1) (by omega))
  have hF : Tendsto (fun n : ℕ => ((f n+u : ℕ) : ℝ)/(n : ℝ)^(d-1)) atTop
      (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))) := by
    simpa only [Nat.cast_add,add_div,add_zero] using
      (exact_conditions_outer_limit hd upper a f e hc).add hfixed
  have hqcount := eventually_count_le_multiple_monomial
    (fun n => Fintype.card (PreparedParameters.Label (upperCount n d)
      (PreparedParameters.allEvenIndices d) (PreparedParameters.allEvenCount d h n (e n+extraSlots)))) 1 d _ hS (by
      simpa only [Nat.cast_one,one_mul,one_div] using
        div_lt_div_of_pos_right hρ (show (0 : ℝ)<d.factorial by positivity))
  have hfcount := eventually_count_le_multiple_monomial (fun n => f n+u) h (d-1) _ hF (by
    have hmul := mul_lt_mul_of_pos_left hρ (show (0 : ℝ)<h by exact_mod_cast hh)
    simpa only [mul_one,div_eq_mul_inv] using
      div_lt_div_of_pos_right hmul (show (0 : ℝ)<(d-1).factorial by positivity))
  filter_upwards [hqcount,hfcount,eventually_gt_atTop (0 : ℕ)] with n hn hfn hnpos
  intro O hO
  apply prepared_independent_open (by omega) hO
    (fun j hj => (PreparedParameters.mem_allEvenIndices.mp hj).2.1)
    (fun j hj => by have := (PreparedParameters.mem_allEvenIndices.mp hj).1; omega)
  · rw [finrank_forms K n d hnpos]
    simpa only [one_mul] using hn
  · simpa only [Rows,Module.finrank_pi_fintype,Fintype.card_fin,
      finrank_forms K n (d-1) hnpos,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] using hfn

end Froberg.PreparedTarget
