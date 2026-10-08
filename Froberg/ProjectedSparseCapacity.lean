import Froberg.QuadraticSparseBudget
import Froberg.SmallSparseLayerBudget

/-! The same selected sparse blocks retain their capacity after quotienting
by one output linear form. The loss has one lower polynomial degree. -/
noncomputable section
namespace Froberg
open Filter Polynomial
open scoped Topology

theorem affine_monomial_count_normalized_small {e d a : ℕ} (ha : 0<a) (hed : e<d) :
    Tendsto (fun n : ℕ => ((a*n+e-1).choose e : ℝ)/(n : ℝ)^d) atTop (𝓝 0) := by
  have hdeg : (affineCountPolynomial e a 0).degree < (X^d : ℝ[X]).degree := by
    apply degree_lt_degree
    rw [affineCountPolynomial_natDegree e (by exact_mod_cast ha.ne'),natDegree_X_pow]
    exact hed
  have ht := ((affineCountPolynomial e a 0).div_tendsto_atTop_zero_of_degree_lt
    (X^d) hdeg).comp tendsto_natCast_atTop_atTop
  have heval (n : ℕ) : (affineCountPolynomial e a 0).eval (n : ℝ)=((a*n+e-1).choose e : ℝ) := by
    simpa only [Nat.cast_zero,add_zero] using affineCountPolynomial_eval e a 0 n
  simpa only [Function.comp_def,heval,eval_pow,eval_X] using ht

/-- A strict sparse incidence margin absorbs any output loss of smaller
order, while preserving the already selected block count. -/
theorem eventually_sparse_projected_capacity
    (b H loss : ℕ → ℕ) {C c R : ℕ} (hc : c≤C) (rho delta : ℝ)
    (hdelta : 0<delta) (hCrho : 0<(C : ℝ)*rho)
    (hH : Tendsto (fun n : ℕ => (H n : ℝ)/(n : ℝ)^R) atTop (𝓝 delta))
    (hloss : Tendsto (fun n : ℕ => (loss n : ℝ)/(n : ℝ)^R) atTop (𝓝 0))
    (hmargin : ∀ᶠ n : ℕ in atTop,
      (b n : ℝ)*C+(H n : ℝ)*C*rho<H n) :
    ∀ᶠ n : ℕ in atTop, b n*c≤H n-loss n := by
  have hbig := hH.mul_const ((C : ℝ)*rho)
  have hbig' : Tendsto (fun n : ℕ => ((H n : ℝ)*C*rho)/(n : ℝ)^R)
      atTop (𝓝 (delta*((C : ℝ)*rho))) := by
    apply hbig.congr'
    exact Eventually.of_forall fun n => by dsimp only; ring
  filter_upwards [hmargin,eventually_lt_of_normalized_limits _ _ R _ _ hloss hbig'
    (mul_pos hdelta hCrho)] with n hn hl
  have hnat : b n*c≤b n*C := Nat.mul_le_mul_left (b n) hc
  have hnatR : (b n : ℝ)*c≤(b n : ℝ)*C := by exact_mod_cast hnat
  have hsumR : (b n : ℝ)*c+loss n≤H n := by linarith
  have hsum : b n*c+loss n≤H n := by exact_mod_cast hsumR
  omega

theorem eventually_quadratic_sparse_projected_capacity {d : ℕ} (hd : 3≤d) :
    ∀ᶠ h : ℕ in atTop,
      fullSparseBlockCount (countBeta d) 2 (d-2) h*(d-2+1).choose (d-2) ≤
        quadraticOutputDimension d h-h := by
  apply eventually_sparse_projected_capacity
    (fun h => fullSparseBlockCount (countBeta d) 2 (d-2) h)
    (quadraticOutputDimension d) (fun h => h)
    (C := scalarCapacityBinomial d 2) (R := 2) ?_
    (criticalRatio d) (quadraticOutputDensity d)
    (lt_trans (by norm_num) (quadraticOutputDensity_lower hd)) ?_
    (quadraticOutputDimension_limit hd) ?_
  · exact (eventually_quadratic_sparse_margin hd).mono (fun h hh => hh.2.2)
  · unfold scalarCapacityBinomial
    exact Nat.choose_le_choose (d-2) (by omega)
  · have hC : 0<scalarCapacityBinomial d 2 := by
      unfold scalarCapacityBinomial
      exact Nat.choose_pos (by omega)
    exact mul_pos (by exact_mod_cast hC) (criticalRatio_bounds (by omega : 2≤d)).1
  · simpa only [Nat.one_mul,Nat.add_sub_cancel,Nat.choose_one_right] using
      affine_monomial_count_normalized_small (a := 1) (e := 1) (d := 2) (by omega) (by omega)

theorem eventually_higher_sparse_projected_capacity {d R : ℕ} (hd : 3≤d)
    (hR : R∈activeHigherIndices d) :
    ∀ᶠ w : ℕ in atTop,
      sparseBlockCount ((101/100 : ℝ)*higherCountGamma d R) R (d-R) w*(d-R+1).choose (d-R) ≤
        oddOutputDimension w R-(2*w+(R-1)-1).choose (R-1) := by
  have hactive := activeEvenIndices_bounds hd (Finset.mem_filter.mp hR).1
  have hRpos : 0<R := by omega
  apply eventually_sparse_projected_capacity
    (fun w => sparseBlockCount ((101/100 : ℝ)*higherCountGamma d R) R (d-R) w)
    (fun w => oddOutputDimension w R) (fun w => (2*w+(R-1)-1).choose (R-1))
    (C := scalarCapacityBinomial d R) (R := R) ?_
    (criticalRatio d) (2^(R-1)/(R.factorial : ℝ)) (by positivity) ?_
    (oddOutputDimension_normalized_limit hRpos)
    (affine_monomial_count_normalized_small (by omega : 0<2) (by omega : R-1<R))
  · exact (eventually_sparse_odd_margin (by omega : 2≤d) hRpos hactive.2.1.le
      ((101/100 : ℝ)*higherCountGamma d R)
      (mul_nonneg (by norm_num) (higherCountGamma_pos d R).le)
      (higher_sparse_scalar_margin_all hd hR)).mono (fun w hw => hw.2.2)
  · unfold scalarCapacityBinomial
    exact Nat.choose_le_choose (d-R) (by omega)
  · have hC : 0<scalarCapacityBinomial d R := by
      unfold scalarCapacityBinomial
      exact Nat.choose_pos (by omega)
    exact mul_pos (by exact_mod_cast hC) (criticalRatio_bounds (by omega : 2≤d)).1

end Froberg
