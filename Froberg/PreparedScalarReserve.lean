import Froberg.PreparedCountIdentities

/-! The additional scalar labels in the prepared family have degree at
most d-2, so their cost is negligible against the second-order outer
reserve even after adjoining any fixed number of labels. -/
noncomputable section
namespace Froberg
open Filter Polynomial
open scoped Topology

theorem prepared_extra_scalar_count_lower_order {d : ℕ} (hd : 3≤d) (h extra : ℕ)
    (e : ℕ → ℕ)
    (he : ∀ᶠ m : ℕ in atTop,(e m : ℝ)<countBeta d*(h : ℝ)^2*(m : ℝ)^(d-2)) :
    Tendsto (fun m : ℕ =>
      ((e m+(∑ j∈activeHigherIndices d,higherGeneratorCount d h m j)+extra : ℕ) : ℝ)/(m : ℝ)^(d-1))
      atTop (𝓝 0) := by
  let P : Polynomial ℝ := monomial (d-2) (countBeta d*(h : ℝ)^2)
  have hp : P.natDegree<d-1 := (natDegree_monomial_le _).trans_lt (by omega)
  have hlim : Tendsto (fun m : ℕ =>
      (countBeta d*(h : ℝ)^2*(m : ℝ)^(d-2))/(m : ℝ)^(d-1)) atTop (𝓝 0) := by
    simpa only [P,eval_monomial,coeff_eq_zero_of_natDegree_lt hp] using
      polynomial_div_pow_nat_tendsto P (d-1) hp.le
  have hE : Tendsto (fun m : ℕ => (e m : ℝ)/(m : ℝ)^(d-1)) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => by positivity)
      (he.mono fun m hm => div_le_div_of_nonneg_right hm.le (by positivity)) hlim
  have hS : Tendsto (fun m : ℕ =>
      ((extra+∑ j∈activeHigherIndices d,higherGeneratorCount d h m j : ℕ) : ℝ)/(m : ℝ)^(d-1))
      atTop (𝓝 0) := by
    apply auxiliary_counts_lower_order (activeHigherIndices d) (by omega)
      (fun j => (101/100 : ℝ)*higherCountGamma d j*(h : ℝ)^j)
      (fun j => d-j) extra
    · intro j _
      exact mul_nonneg (mul_nonneg (by norm_num) (higherCountGamma_pos d j).le) (by positivity)
    · intro j hj
      have := (Finset.mem_filter.mp hj).2
      omega
  have ht := hE.add hS
  simp only [add_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall fun m => by
    simp only [Nat.cast_add,add_div]
    ring

theorem prepared_scalar_difference_lower_order {d : ℕ} (hd : 3≤d) (h extra : ℕ)
    (e : ℕ → ℕ)
    (he : ∀ᶠ m : ℕ in atTop,(e m : ℝ)<countBeta d*(h : ℝ)^2*(m : ℝ)^(d-2)) :
    Tendsto (fun m : ℕ =>
      ((preparedScalarCount d h m (e m)+extra-upperCount m d : ℕ) : ℝ)/(m : ℝ)^(d-1))
      atTop (𝓝 0) := by
  have hid (m : ℕ) : preparedScalarCount d h m (e m)+extra-upperCount m d=
      e m+(∑ j∈activeHigherIndices d,higherGeneratorCount d h m j)+extra := by
    unfold preparedScalarCount
    omega
  simpa only [hid] using prepared_extra_scalar_count_lower_order hd h extra e he

end Froberg
