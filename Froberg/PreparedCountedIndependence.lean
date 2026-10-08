import Froberg.PreparedIndependenceOpen
import Froberg.PreparedScalarReserve
import Froberg.ExactOuterLimit

/-! The manuscript's actual scalar and vector counts lie strictly below
their ambient dimensions, giving independence on the same parameter space. -/
noncomputable section
namespace Froberg
open Filter Module MvPolynomial Quartic VectorMultiplicationCoordinates
open scoped Topology

theorem eventually_count_le_multiple_monomial (r : ℕ → ℕ) (a s : ℕ) (c : ℝ)
    (hr : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^s) atTop (𝓝 c))
    (hgap : c<(a : ℝ)*(s.factorial : ℝ)⁻¹) :
    ∀ᶠ n : ℕ in atTop,r n≤a*(n+s-1).choose s := by
  have hb := hr.eventually_lt ((monomial_count_normalized_tendsto s).const_mul (a : ℝ)) hgap
  filter_upwards [hb,eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hnR : (0 : ℝ)<n := by exact_mod_cast hnpos
  have hh : (r n : ℝ)<(a : ℝ)*((n+s-1).choose s : ℝ) := by
    apply (div_lt_div_iff_of_pos_right (pow_pos hnR s)).mp
    simpa only [mul_div_assoc] using hn
  exact_mod_cast hh.le

namespace PreparedTarget
variable {K : Type} [Field K] [Infinite K]

theorem exact_counts_prepared_independent_open {d k h lo u : ℕ}
    (hd : 3≤d) (hh : 0<h) (upper : Bool) (a f e : ℕ → ℕ)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    (O : ℕ → Submodule K (Poly K h)) (hO : ∀ j∈activeEvenIndices d,O j≤Forms K h j) :
    ∀ᶠ n : ℕ in atTop,HasIndependentOpen (m := n) (q := upperCount n d)
      (f := f n) (u := u) (counts := targetLayerCount d h n (e n)) (by omega : 0<d) hO
      (fun j hj => (activeEvenIndices_bounds hd hj).2.1.le) := by
  have hρ := (criticalRatio_bounds (show 2≤d by omega)).2.1
  have he := hc.mono fun n hn => hn.quadratic_upper
  have hS : Tendsto (fun n : ℕ => (preparedScalarCount d h n (e n) : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ))) := by
    simpa only [Nat.add_zero] using preparedScalarCount_normalized_limit hd h 0 e he
  have hfixed : Tendsto (fun n : ℕ => (u : ℝ)/(n : ℝ)^(d-1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (nat_power_tendsto_atTop (d-1) (by omega))
  have hF : Tendsto (fun n : ℕ => ((f n+u : ℕ) : ℝ)/(n : ℝ)^(d-1)) atTop
      (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))) := by
    simpa only [Nat.cast_add,add_div,add_zero] using
      (exact_conditions_outer_limit hd upper a f e hc).add hfixed
  have hqcount := eventually_count_le_multiple_monomial
    (fun n => preparedScalarCount d h n (e n)) 1 d _ hS (by
      simpa only [Nat.cast_one,one_mul,one_div] using
        div_lt_div_of_pos_right hρ (show (0 : ℝ)<d.factorial by positivity))
  have hfcount := eventually_count_le_multiple_monomial (fun n => f n+u) h (d-1) _ hF (by
    have hmul := mul_lt_mul_of_pos_left hρ (show (0 : ℝ)<h by exact_mod_cast hh)
    simpa only [mul_one,div_eq_mul_inv] using
      div_lt_div_of_pos_right hmul (show (0 : ℝ)<(d-1).factorial by positivity))
  filter_upwards [hqcount,hfcount,eventually_gt_atTop (0 : ℕ)] with n hn hfn hnpos
  apply prepared_independent_open (by omega) hO
    (fun j hj => (activeEvenIndices_bounds hd hj).2.1.le)
    (fun j hj => by have := (activeEvenIndices_bounds hd hj).1; omega)
  · rw [←preparedScalarCount_eq_card hd,finrank_forms K n d hnpos]
    simpa only [one_mul] using hn
  · simpa only [Rows,Module.finrank_pi_fintype,Fintype.card_fin,
      finrank_forms K n (d-1) hnpos,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] using hfn

end PreparedTarget
end Froberg
