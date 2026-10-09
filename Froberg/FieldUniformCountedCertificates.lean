module

public import Froberg.RestoredCountedOuterOdd
public import Froberg.PreparedCountedOddCycles
public import Froberg.FieldUniformCountedRows
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

theorem uniform_exact_counts_all_even_odd_open {d k h lo u : ℕ}
    (hd : 3≤d) (hdodd : d%2=1) (hk : 0<k)
    (hh : h=k*centralHalfBinomial d) (hhpos : 0<h)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n,a n≤n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0<δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n))
    (extraSlots : ℕ) :
    ∀ᶠ n : ℕ in atTop,∀ (K : Type) [Field K] [Infinite K],∀ (O : ℕ → Submodule K (Poly K h))
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
  have hscalar := eventually_uniform_odd_scalar_layers_open hd hhpos qS (fun n => f n+u) hS hF
  have hupper := eventually_upper_odd_row_budget hd hhpos (fun n => f n+u) hF
  have hcapacity := VectorExpansionOpen.eventually_field_uniform_augmented_outer_capacity (b := u)
    hd f extra hδ hextra hreserve
  obtain ⟨G,hG,hmodels⟩ := uniform_exact_counts_private_strict_open (b := u)
    hd hk hh upper a f e ha hc
  filter_upwards [hscalar,hupper,hcapacity,hmodels,eventually_gt_atTop (0 : ℕ)]
    with n hsn hun hcn hmn hn
  intro K _ _ O hO
  obtain ⟨D,hD,hmodel⟩ := hmn K
  obtain ⟨E,hE,hEmodel⟩ := VectorParameters.principal_open_in_finite_coordinates D hD
    (fun g => VectorExpansionOpen.StrictModel g d (G*(n : ℝ)^d) ∧
      Fintype.card (PreparedParameters.Label (upperCount n d) (PreparedParameters.allEvenIndices d)
        (PreparedParameters.allEvenCount d h n (e n+extraSlots)))*finrank K (VectorExpansionOpen.Source g)≤
          finrank K (VectorExpansionOpen.Target g d)) (by
      intro p hp
      refine ⟨hmodel p hp,?_⟩
      have hh := hcn K (G*(n : ℝ)^d) (VectorParameters.generators p) (hmodel p hp)
      rwa [hcount] at hh)
  apply prepared_odd_cycles_open hhpos hn hd hdodd hO
    (fun j hj => (PreparedParameters.mem_allEvenIndices.mp hj).2.1)
    (fun j hj => by have := (PreparedParameters.mem_allEvenIndices.mp hj).1; omega)
    (fun j hj => (PreparedParameters.mem_allEvenIndices.mp hj).2.2) E hE hEmodel
  · exact hsn K
  · exact hun


end Froberg.PreparedTarget

namespace Froberg.PreparedParameters
open Froberg Filter Module MvPolynomial Quartic VectorMultiplicationCoordinates
open scoped Topology

theorem uniform_exact_counts_restored_outer_odd_open {d k h lo : ℕ}
    (hd : 3≤d) (hdeven : d%2=0) (hk : 0<k) (hh : h=k*centralHalfBinomial d) (hhpos : 0<h)
    (upper : Bool) (a f e extra : ℕ → ℕ) (ha : ∀ n,a n≤n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0<δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n))
    (hextra : Tendsto (fun n : ℕ => (extra n : ℝ)/(n : ℝ)^(d-1)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,∀ (K : Type) [Field K] [Infinite K],∀ (q : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
      (O : ℕ → Submodule K (Poly K h))
      (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (hpos : ∀ j∈J,0<j) (heven : ∀ j∈J,j%2=0)
      (idx : Fin (upperCount n d+extra n) ≃ Label q J counts)
      (slot : Fin (finrank K (Forms K h d)) → Fin (upperCount n d+extra n)),
      HasRestoredOuterOddOpen (m := n) (f := f n) (by omega) hdeven hO hJ heven idx slot := by
  have hopen := uniform_exact_counts_scalar_vector_rows_open (b := 0)
    hd hk hh hhpos upper a f e extra ha hc hδ hreserve hextra
  simp only [Nat.add_zero] at hopen
  filter_upwards [hopen] with n hn
  intro K _ _ q J counts O hO hJ hpos heven idx slot
  obtain ⟨P,hP,hgood⟩ := hn K
  exact restored_outer_odd_open_of_rows hd hdeven hO hJ hpos heven idx slot P hP hgood

theorem uniform_exact_counts_all_even_restored_odd_open {d k h lo : ℕ}
    (hd : 3≤d) (heven : d%2=0) (hk : 0<k) (hh : h=k*centralHalfBinomial d) (hhpos : 0<h)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n,a n≤n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0<δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n))
    (added : ℕ) :
    ∀ᶠ n : ℕ in atTop,∀ (K : Type) [Field K] [Infinite K],∀ (O : ℕ → Submodule K (Poly K h))
      (hO : ∀ j∈allEvenIndices d,O j≤Forms K h j)
      (slot : Fin (finrank K (Forms K h d)) →
        Fin (Fintype.card (Label (upperCount n d) (allEvenIndices d) (allEvenCount d h n (e n+added))))),
      HasRestoredOuterOddOpen (m := n) (f := f n) (by omega : 1≤d) heven hO
        (fun j hj => (mem_allEvenIndices.mp hj).2.1)
        (fun j hj => (mem_allEvenIndices.mp hj).2.2) (Fintype.equivFin _).symm slot := by
  let extra := fun n => e n+(∑ j∈activeHigherIndices d,higherGeneratorCount d h n j)+added
  have he := hc.mono fun n hn => hn.quadratic_upper
  have hextra := prepared_extra_scalar_count_lower_order hd h added e he
  have hopen := uniform_exact_counts_restored_outer_odd_open hd heven hk hh hhpos
    upper a f e extra ha hc hδ hreserve hextra
  filter_upwards [hopen] with n hn
  have hcard : upperCount n d+extra n=
      Fintype.card (Label (upperCount n d) (allEvenIndices d) (allEvenCount d h n (e n+added))) := by
    rw [allEvenLabel_card hd,preparedLabel_card,sum_targetLayerCount hd]
    dsimp only [extra]
    omega
  rw [hcard] at hn
  intro K _ _ O hO slot
  exact hn K (upperCount n d) (allEvenIndices d) (allEvenCount d h n (e n+added)) O hO
    (fun j hj => (mem_allEvenIndices.mp hj).2.1)
    (fun j hj => by have := (mem_allEvenIndices.mp hj).1; omega)
    (fun j hj => (mem_allEvenIndices.mp hj).2.2) (Fintype.equivFin _).symm slot

end Froberg.PreparedParameters
