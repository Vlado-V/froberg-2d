module

public import Froberg.CountedFourthRow
public import Froberg.PreparedFourthRow
public import Froberg.ShiftedPreparedCapacities
public import Froberg.ShiftedSmallCapacities
public import Froberg.ShiftedSparseBudgets
public import Froberg.SingleProfileScalar

@[expose] public section

/-! Fourth-row capacity thresholds precede the choice of output constraints. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
open Quartic.PolynomialBilinearCoordinates
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

theorem eventually_counted_fourth_row_capacity_shift_late_output {d : ℕ}
    (hd : 5 ≤ d) (hd8 : d ≤ 8) :
    ∀ᶠ w : ℕ in atTop,
      ∀ (z extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ v : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) → T 4=0 →
        FourthRowCapacity w v d (upperCount (v+v+z) d)
          (sparseBlockCount ((101/100 : ℝ)*higherCountGamma d 4) 4 (d-4) w)
          (allEvenIndices d) (allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)) T := by
  have h4a : 4∈activeEvenIndices d := by
    simp [activeEvenIndices,hd8,show 4<d by omega]
  have h4h : 4∈activeHigherIndices d := Finset.mem_filter.mpr ⟨h4a,le_rfl⟩
  filter_upwards [eventually_higher_sparse_layer_budget_shift (by omega : 3 ≤ d) h4h,
    tendsto_twice_nat.eventually (eventually_small_quadratic_diagonal_capacity_shift hd hd8),
    eventually_gt_atTop (0 : ℕ)] with w hsparse hdiag hw
  intro z extra e he
  have hecast : ∀ᶠ n : ℕ in atTop,
      (e n : ℝ)<countBeta d*((2*w : ℕ) : ℝ)^2*(n : ℝ)^(d-2) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using he
  let q : ℕ → ℕ := fun n => upperCount (n+z) d
  let counts : ℕ → ℕ → ℕ := fun n => allEvenCount d (2*w) (n+z) (e (n+z)+extra)
  let r := fun n => Fintype.card (Label (q n) (allEvenIndices d) (counts n))
  have hcount : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ))) :=
    allEvenLabel_count_limit_shift (by omega) (2*w) extra z e hecast
  have hbudget := tendsto_twice_nat.eventually (hsparse.2.2 z 0 r hcount)
  have hdiagonal := tendsto_twice_nat.eventually (hdiag z extra)
  obtain ⟨n₀,hn₀⟩ := eventually_small_single_profile_scalar_open (K := K)
    (by omega : 3 ≤ d) hd8 (R := 4) (Or.inl rfl) (by omega) r hcount
  filter_upwards [hbudget,hdiagonal,
    tendsto_twice_nat.eventually ((tendsto_add_atTop_nat z).eventually hecast),
    eventually_gt_atTop (0 : ℕ),eventually_ge_atTop n₀] with v hb hdiagv hev hv hvlarge
  intro X _ _ _ T hX hT
  have heceil : e (2*v+z) ≤
      ⌈countBeta d*((2*w : ℕ) : ℝ)^2*((2*v+z : ℕ) : ℝ)^(d-2)⌉₊ := by
    exact_mod_cast hev.le.trans (Nat.le_ceil _)
  have hdiag' : counts (v+v) 2 ≤
      (w.choose 2-finrank K X)*(v.choose (d-2)/2) := by
    have hc := (Nat.add_le_add_right heceil extra).trans hdiagv
    simpa only [counts,allEvenCount_active _ _ _ (two_mem_activeEvenIndices (d := d) (by omega)),
      targetLayerCount,ite_true,two_mul,show (w+w)/2=w by omega,show (v+v)/2=v by omega,
      hX] using hc
  obtain ⟨D,hD,hgood⟩ := hn₀ (v+v) (by omega) (balancedScalarHalf v)
    (by simp only [balancedScalarHalf_card,balancedScalarHalf_compl_card];omega)
    (by simp only [balancedScalarHalf_card,balancedScalarHalf_compl_card];omega)
    (2*((d-2)/2))
  exact { hw := hw
          hv := hv
          low := fun j hj => (mem_allEvenIndices.mp hj).1
          even := fun j hj => Nat.even_iff.mpr (mem_allEvenIndices.mp hj).2.2
          degree := fun j hj => (mem_allEvenIndices.mp hj).2.1
          new_unconstrained := hT
          diagonal := hdiag'
          output_positive := hsparse.1
          enough_generators := by
            simpa only [allEvenCount_active _ _ _ h4a,targetLayerCount,
              if_neg (by decide : (4 : ℕ)≠2),Nat.add_zero,two_mul] using hb.1
          divisor_capacity := hsparse.2.1
          incidence := by simpa only [r,q,counts,two_mul] using hb.2
          scalar_open := ⟨D,hD,hgood⟩ }

end Froberg.PreparedParameters
