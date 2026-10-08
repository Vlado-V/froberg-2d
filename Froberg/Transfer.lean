import Froberg.ProjectedDeformation
import Froberg.GenericMonotonicity

/-! The transfer inequalities, derived from an actual projected polynomial
complex and its first normal map. The construction of such data is separate. -/
noncomputable section
namespace Froberg
open Module

variable {K : Type} [Field K] [Infinite K]
  {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {n d r : ℕ}

/-- The linear-algebra part of Theorem 6.2, with every defect interpreted in
the actual polynomial quotient. -/
theorem transfer_bounds_of_projected_normal
    (hn : 0 < n) (hr : r ≤ (n + d - 1).choose d)
    (π : Forms K n (2 * d) →ₗ[K] W) (q p : Fin r → Forms K n d)
    (hq : LinearIndependent K q) (k₀ a₀ j₀ c₀ : ℕ)
    (hH : finrank K (ProjectedEndpointHomology π q) = k₀ + a₀)
    (hC : finrank K (ProjectedEndpointCokernel π q) = j₀)
    (hTarget : finrank K W + c₀ = (n + 2 * d - 1).choose (2 * d))
    (hNormal : finrank K (projectedNormalMap π q p).range = min a₀ j₀) :
    (genericHomology K n d r : ℤ) ≤ max (k₀ : ℤ) ((c₀ : ℤ) - euler n d r) ∧
    (genericCokernel K n d r : ℤ) ≤ max (c₀ : ℤ) ((k₀ : ℤ) + euler n d r) := by
  obtain ⟨ε, _, hi, hdrop⟩ := exists_projected_normal_homology_drop π q p hq
  have hgeneric := genericHomology_le_family hn (q + ε • p) hi
  rw [hNormal, hH] at hdrop
  have hEuler := projected_endpoint_euler π q hq
  change (finrank K (ProjectedEndpointCokernel π q) : ℤ) -
    (finrank K (ProjectedEndpointHomology π q) : ℤ) = _ at hEuler
  rw [hH, hC, Module.finrank_pi_fintype, finrank_forms K n d hn] at hEuler
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hEuler
  push_cast at hEuler
  have hχ : euler n d r = (c₀ : ℤ) - k₀ + j₀ - a₀ := by
    unfold euler
    omega
  have hGE := generic_euler (K := K) hn hr
  constructor <;> rw [hχ] <;> omega

/-- The sign at each critical count turns the two transfer bounds into the
single decreasing-defect recurrence used by the arithmetic argument. -/
theorem criticalDefect_step_of_transfer {m h d : ℕ}
    (_hm : 0 < m) (hnext : 0 < m + h)
    (hH : (genericHomology K (m + h) d (lowerCount (m + h) d) : ℤ) ≤
      max (criticalDefect K m d : ℤ)
        ((criticalDefect K m d : ℤ) - euler (m + h) d (lowerCount (m + h) d)))
    (hC : (genericCokernel K (m + h) d (upperCount (m + h) d) : ℤ) ≤
      max (criticalDefect K m d : ℤ)
        ((criticalDefect K m d : ℤ) + euler (m + h) d (upperCount (m + h) d))) :
    criticalDefect K (m + h) d ≤ criticalDefect K m d := by
  have hlo := euler_lowerCount_nonneg hnext d
  have hup := euler_upperCount_nonpos hnext d
  have hH' : (genericHomology K (m + h) d (lowerCount (m + h) d) : ℤ) ≤
      (criticalDefect K m d : ℤ) := by
    rw [max_eq_left (by omega)] at hH
    exact hH
  have hC' : (genericCokernel K (m + h) d (upperCount (m + h) d) : ℤ) ≤
      (criticalDefect K m d : ℤ) := by
    rw [max_eq_left (by omega)] at hC
    exact hC
  change max (genericHomology K (m + h) d (lowerCount (m + h) d))
    (genericCokernel K (m + h) d (upperCount (m + h) d)) ≤ criticalDefect K m d
  exact max_le (by exact_mod_cast hH') (by exact_mod_cast hC')

end Froberg
