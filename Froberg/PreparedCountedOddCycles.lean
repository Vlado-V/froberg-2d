module

public import Froberg.PreparedOddCyclesOpen
public import Froberg.PreparedScalarReserve
public import Froberg.VectorModelCoordinates
public import Froberg.AugmentedOuterCapacity

@[expose] public section

/-! The actual scalar, higher-layer, outer and private counts satisfy
every hypothesis of the full prepared odd-cycle open. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedTarget
open Froberg Filter Module MvPolynomial Quartic VectorMultiplicationCoordinates
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

def HasOddCyclesOpen {h m d q f u : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    {O : ℕ → Submodule K (Poly K h)} (hO : ∀ j∈J,O j≤Forms K h j) : Prop :=
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  ∃ P : MvPolynomial (Fin (finrank K
    (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O))) K,
    (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
      eval ((Module.finBasis K _).equivFun p) P≠0) ∧
    ∀ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
      eval ((Module.finBasis K _).equivFun p) P≠0 →
      ∀ U : Fin u → Forms K h d,OddCyclesExact U p.1 p.2

theorem exact_counts_prepared_odd_cycles_open {d k h lo u : ℕ}
    (hd : 3≤d) (hdodd : d%2=1) (hk : 0<k)
    (hh : h=k*centralHalfBinomial d) (hhpos : 0<h)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n,a n≤n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0<δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n))
    (O : ℕ → Submodule K (Poly K h)) (hO : ∀ j∈activeEvenIndices d,O j≤Forms K h j) :
    ∀ᶠ n : ℕ in atTop,HasOddCyclesOpen (m := n) (d := d) (q := upperCount n d)
      (f := f n) (u := u) (counts := targetLayerCount d h n (e n)) hO := by
  let extra := fun n => e n+(∑ j∈activeHigherIndices d,higherGeneratorCount d h n j)+0
  let qS := fun n => preparedScalarCount d h n (e n)
  have he := hc.mono fun n hn => hn.quadratic_upper
  have hextra := prepared_extra_scalar_count_lower_order hd h 0 e he
  have hcount (n : ℕ) : upperCount n d+extra n=qS n := by
    simp only [extra,qS,preparedScalarCount,add_zero]
    omega
  have hcard (n : ℕ) : qS n=Fintype.card (PreparedParameters.Label (upperCount n d)
      (activeEvenIndices d) (targetLayerCount d h n (e n))) := preparedScalarCount_eq_card hd h n (e n)
  have hS : Tendsto (fun n : ℕ => (qS n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ))) := by
    simpa only [Nat.add_zero] using preparedScalarCount_normalized_limit hd h 0 e he
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
  obtain ⟨D,hD,hmodel⟩ := hmn
  obtain ⟨E,hE,hEmodel⟩ := VectorParameters.principal_open_in_finite_coordinates D hD
    (fun g => VectorExpansionOpen.StrictModel g d (G*(n : ℝ)^d) ∧
      Fintype.card (PreparedParameters.Label (upperCount n d) (activeEvenIndices d)
        (targetLayerCount d h n (e n)))*finrank K (VectorExpansionOpen.Source g)≤
          finrank K (VectorExpansionOpen.Target g d)) (by
      intro p hp
      refine ⟨hmodel p hp,?_⟩
      have hh := hcn (G*(n : ℝ)^d) (VectorParameters.generators p) (hmodel p hp)
      rwa [hcount,hcard] at hh)
  apply prepared_odd_cycles_open hhpos hn hd hdodd hO
    (fun j hj => (activeEvenIndices_bounds hd hj).2.1.le)
    (fun j hj => by have := (activeEvenIndices_bounds hd hj).1; omega)
    (fun j hj => by
      obtain ⟨_,_,k,hk⟩ := activeEvenIndices_bounds hd hj
      omega) E hE hEmodel
  · simpa only [hcard] using hsn
  · exact hun

end Froberg.PreparedTarget
