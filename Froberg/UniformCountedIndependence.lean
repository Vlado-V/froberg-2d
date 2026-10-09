module

public import Froberg.CountedAllEvenCertificates

@[expose] public section

/-! The actual family is independent after one numerical threshold,
chosen uniformly over all infinite fields and output constraints. -/
noncomputable section
namespace Froberg.PreparedTarget
open Froberg Filter Module MvPolynomial Quartic VectorMultiplicationCoordinates
open scoped Topology

theorem uniform_exact_counts_all_even_independent_open {d k h lo u : ℕ}
    (hd : 3≤d) (hh : 0<h) (upper : Bool) (a f e : ℕ → ℕ)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    (extraSlots : ℕ) :
    ∀ᶠ n : ℕ in atTop,∀ (K : Type) [Field K] [Infinite K], ∀ (O : ℕ → Submodule K (Poly K h))
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
  intro K _ _ O hO
  apply prepared_independent_open (by omega) hO
    (fun j hj => (PreparedParameters.mem_allEvenIndices.mp hj).2.1)
    (fun j hj => by have := (PreparedParameters.mem_allEvenIndices.mp hj).1; omega)
  · rw [finrank_forms K n d hnpos]
    simpa only [one_mul] using hn
  · simpa only [Rows,Module.finrank_pi_fintype,Fintype.card_fin,
      finrank_forms K n (d-1) hnpos,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] using hfn


end Froberg.PreparedTarget
