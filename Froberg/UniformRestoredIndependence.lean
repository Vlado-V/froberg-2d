module

public import Froberg.RestoredOuterIndependence
public import Froberg.PreparedCountedIndependence
public import Froberg.PreparedAllEvenCounts

@[expose] public section

/-! Actual all-even counts make the whole restored endpoint independent
on a nonempty open, including any fixed number of added quadratic slots. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Filter Module MvPolynomial Quartic VectorMultiplicationCoordinates
open scoped Topology

theorem uniform_exact_counts_actual_restored_independent_open {d k h lo : ℕ}
    (hd : 3≤d) (hdeven : d%2=0) (hh : 0<h)
    (upper : Bool) (a f e : ℕ → ℕ) (added : ℕ)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) :
    ∀ᶠ n : ℕ in atTop,∀ (K : Type) [Field K] [Infinite K], ∀ (O : ℕ → Submodule K (Poly K h))
      (hO : ∀ j∈allEvenIndices d,O j≤Forms K h j)
      (slot : Fin (finrank K (Forms K h d)) →
        Fin (Fintype.card (Label (upperCount n d) (allEvenIndices d) (allEvenCount d h n (e n+added))))),
      HasRestoredIndependentOpen (m := n) (f := f n) (by omega) hdeven hO
        (fun j hj => (mem_allEvenIndices.mp hj).2.1)
        (fun j hj => (mem_allEvenIndices.mp hj).2.2) (Fintype.equivFin _).symm slot := by
  have hρ := (criticalRatio_bounds (show 2≤d by omega)).2.1
  have hS := allEvenLabel_count_limit hd h added e (hc.mono fun n hn => hn.quadratic_upper)
  have hF := exact_conditions_outer_limit hd upper a f e hc
  have hqcount := eventually_count_le_multiple_monomial
    (fun n => Fintype.card (Label (upperCount n d) (allEvenIndices d) (allEvenCount d h n (e n+added))))
    1 d _ hS (by
      simpa only [Nat.cast_one,one_mul,one_div] using
        div_lt_div_of_pos_right hρ (show (0 : ℝ)<d.factorial by positivity))
  have hfcount := eventually_count_le_multiple_monomial f h (d-1) _ hF (by
    have hmul := mul_lt_mul_of_pos_left hρ (show (0 : ℝ)<h by exact_mod_cast hh)
    simpa only [mul_one,div_eq_mul_inv] using
      div_lt_div_of_pos_right hmul (show (0 : ℝ)<(d-1).factorial by positivity))
  filter_upwards [hqcount,hfcount,eventually_gt_atTop (0 : ℕ)] with n hn hfn hnpos
  intro K _ _ O hO slot
  apply restored_outer_independent_open (by omega) hdeven hO
    (fun j hj => (mem_allEvenIndices.mp hj).2.1)
    (fun j hj => (mem_allEvenIndices.mp hj).2.2)
    (fun j hj => by have := (mem_allEvenIndices.mp hj).1; omega)
    (Fintype.equivFin _).symm slot
  · simpa only [finrank_forms K n d hnpos,one_mul] using hn
  · simpa only [Rows,Module.finrank_pi_fintype,Fintype.card_fin,
      finrank_forms K n (d-1) hnpos,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] using hfn

end Froberg.PreparedParameters
