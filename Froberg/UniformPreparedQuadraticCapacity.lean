import Froberg.ShiftedPreparedCapacities

/-! Actual shifted quadratic counts, uniformly in the output detector. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

theorem eventually_actual_quadratic_capacity_shift_uniform {d : ℕ} (hd : 3≤d) :
    ∀ᶠ w : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) →
      ∀ (z extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ v : ℕ in atTop,
        QuadraticRowCapacity (v+v) d (upperCount (v+v+z) d)
          (fullSparseBlockCount (countBeta d) 2 (d-2) (2*w)) (allEvenIndices d)
          (allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)) (constrainedOutputs T) := by
  filter_upwards [tendsto_twice_nat.eventually
    (eventually_quadratic_capacity_shift (K := K) hd)] with w hquad
  intro X _ _ _ T hO z extra e he
  have hecast : ∀ᶠ n : ℕ in atTop,
      (e n : ℝ)<countBeta d*((2*w : ℕ):ℝ)^2*(n : ℝ)^(d-2) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using he
  let q := fun n => upperCount (n+z) d
  let counts := fun n => allEvenCount d (2*w) (n+z) (e (n+z)+extra)
  have hcount := allEvenLabel_count_limit_shift hd (2*w) extra z e hecast
  filter_upwards [tendsto_twice_nat.eventually
    (hquad (Fin w × Bool) (constrainedOutputs T) hO (allEvenIndices d) q counts hcount z extra),
    tendsto_twice_nat.eventually ((tendsto_add_atTop_nat z).eventually hecast)] with v hv hev
  have hb : e (2*v+z)≤⌈countBeta d*((2*w : ℕ):ℝ)^2*((2*v+z : ℕ):ℝ)^(d-2)⌉₊ := by
    exact_mod_cast hev.le.trans (Nat.le_ceil _)
  have hc : counts (2*v) 2≤⌈countBeta d*((2*w : ℕ):ℝ)^2*((2*v+z : ℕ):ℝ)^(d-2)⌉₊+extra := by
    simpa only [counts,allEvenCount_active _ _ _ (two_mem_activeEvenIndices hd),
      targetLayerCount,ite_true] using Nat.add_le_add_right hb extra
  simpa only [q,counts,two_mul] using hv hc

end Froberg.PreparedParameters
