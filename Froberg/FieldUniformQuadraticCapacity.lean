module

public import Froberg.LatePreparedQuadraticCapacity

@[expose] public section

/-! The scalar threshold for a quadratic row precedes the choice of its
output variable type and quadratic output subspace. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
open Quartic.PolynomialBilinearCoordinates
open scoped Topology

theorem eventually_field_uniform_quadratic_capacity_shift_late {d : ℕ} (hd : 3≤d) :
    ∀ᶠ h : ℕ in atTop,∀ (J : Finset ℕ) (q : ℕ → ℕ) (counts : ℕ → ℕ → ℕ),
      Tendsto (fun n : ℕ => (Fintype.card (Label (q n) J (counts n)) : ℝ)/(n : ℝ)^d)
        atTop (𝓝 (criticalRatio d/(d.factorial : ℝ))) →
      ∀ z extra : ℕ,∀ᶠ n : ℕ in atTop,
        ∀ (K : Type) [Field K] [Infinite K], ∀ (σ : Type*) [Fintype σ],∀ (O : ℕ → Submodule K (MvPolynomial σ K)),
        finrank K (O 2)=quadraticOutputDimension d h →
        counts n 2≤⌈countBeta d*(h : ℝ)^2*((n+z : ℕ) : ℝ)^(d-2)⌉₊+extra →
        QuadraticRowCapacity n d (q n) (fullSparseBlockCount (countBeta d) 2 (d-2) h)
          J (counts n) O := by
  have hβ : 0≤countBeta d := by
    have hG := (countTauFour_pos hd).trans_le (countTauFour_le_gamma d)
    unfold countBeta
    positivity
  filter_upwards [eventually_quadratic_sparse_layer_budget hd,
    eventually_gt_atTop (0 : ℕ)] with h hh hhpos
  intro J q counts hcount z extra
  let r := fun n => Fintype.card (Label (q n) J (counts n))
  have hbudget := hh.2.2 r hcount
  have hscalar := eventually_critical_scalar_incidence_budget (by omega : 2≤d) r hcount
  have hcover := fullSparseBlockCount_eventually_covers_shift_add (countBeta d) hβ 2 h z extra
    (by omega : 0<d-2)
  filter_upwards [hbudget,hscalar,hcover,eventually_gt_atTop (0 : ℕ),
    eventually_ge_atTop ((d-2+d).choose (d-2)*((d-2+d).choose (d-2)*d.choose (d-2)))]
    with n hbudget hscalar hcover hn hlarge
  intro K _ _ σ inst O hO hc
  have hinc := (hbudget 0 (by
    have hp : 0<countBeta d := by
      have hG := (countTauFour_pos hd).trans_le (countTauFour_le_gamma d)
      unfold countBeta
      positivity
    simpa only [Nat.cast_zero] using mul_pos (mul_pos hp (pow_pos (show (0:ℝ)<(h:ℝ) from by exact_mod_cast hhpos) 2))
      (pow_pos (show (0:ℝ)<(n:ℝ) from by exact_mod_cast hn) (d-2)))).2
  have hr : r n*(n+(d-2)-1).choose (d-2)≤(n+(d+(d-2))-1).choose (d+(d-2)) := by
    have he : 2*d-2=d+(d-2) := by omega
    rw [he] at hscalar
    nlinarith
  obtain ⟨D,hD,hgood⟩ := prefix_injective_principal_open (K := K) hn
    (by omega : d-2<d) hlarge hr
  exact { variables_positive := hn
          output_positive := by simpa only [hO] using hh.1
          enough_generators := hc.trans hcover
          divisor_capacity := by simpa only [hO] using hh.2.1
          incidence := by simpa only [hO,r] using hinc
          scalar_open := ⟨D,hD,hgood⟩ }

theorem eventually_field_uniform_actual_quadratic_capacity_shift_late {d : ℕ} (hd : 3≤d) :
    ∀ᶠ w : ℕ in atTop,
      ∀ (z extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ v : ℕ in atTop,
      ∀ (K : Type) [Field K] [Infinite K], ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) →
        QuadraticRowCapacity (v+v) d (upperCount (v+v+z) d)
          (fullSparseBlockCount (countBeta d) 2 (d-2) (2*w)) (allEvenIndices d)
          (allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)) (constrainedOutputs T) := by
  filter_upwards [tendsto_twice_nat.eventually
    (eventually_field_uniform_quadratic_capacity_shift_late hd)] with w hquad
  intro z extra e he
  have hecast : ∀ᶠ n : ℕ in atTop,
      (e n : ℝ)<countBeta d*((2*w : ℕ):ℝ)^2*(n : ℝ)^(d-2) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using he
  let q := fun n => upperCount (n+z) d
  let counts := fun n => allEvenCount d (2*w) (n+z) (e (n+z)+extra)
  have hcount := allEvenLabel_count_limit_shift hd (2*w) extra z e hecast
  filter_upwards [tendsto_twice_nat.eventually
    (hquad (allEvenIndices d) q counts hcount z extra),
    tendsto_twice_nat.eventually ((tendsto_add_atTop_nat z).eventually hecast)] with v hv hev
  intro K _ _ X _ _ _ T hO
  have hb : e (2*v+z)≤⌈countBeta d*((2*w : ℕ):ℝ)^2*((2*v+z : ℕ):ℝ)^(d-2)⌉₊ := by
    exact_mod_cast hev.le.trans (Nat.le_ceil _)
  have hc : counts (2*v) 2≤⌈countBeta d*((2*w : ℕ):ℝ)^2*((2*v+z : ℕ):ℝ)^(d-2)⌉₊+extra := by
    simpa only [counts,allEvenCount_active _ _ _ (two_mem_activeEvenIndices hd),
      targetLayerCount,ite_true] using Nat.add_le_add_right hb extra
  simpa only [q,counts,two_mul] using hv K (Fin w × Bool) (constrainedOutputs T) hO hc

end Froberg.PreparedParameters
