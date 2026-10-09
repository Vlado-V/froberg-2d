module

public import Froberg.PreparedActualMiddleSmallReduction
public import Froberg.LateCountedFourthRow
public import Froberg.LateQuadraticCapacity

@[expose] public section

/-! Scalar thresholds in the small degrees precede the choice of the
output module and all output constraints. -/
noncomputable section
set_option maxHeartbeats 2400000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

theorem eventually_actual_middle_small_witnesses_shift_late_output {d : ℕ}
    (hd : 5≤d) (hd8 : d≤8) :
    ∀ᶠ w : ℕ in atTop,4∣2*w →
      ∀ (z extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ v : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) →
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) →
      T 4=0 →
        let A := Space (v+v) d (upperCount (v+v+z) d) (allEvenIndices d)
          (allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)) (constrainedOutputs T)
        (∀ R : allEvenIndices d,∃ p : A,
          LinearIndependent K (fun i => intrinsicLayerMap (fun _ _ => inf_le_left) R i p) ∧
          (row (fun _ _ => inf_le_left) R p).ker=(rowConstants (fun _ _ => inf_le_left) R p).range) ∧
        (∀ R,d<R → R≤2*d → R%2=0 → ∃ p : A,
          Function.Injective (ProductRows.multiplication
            (allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)) (layers p) (allEvenIndices d) R)) := by
  classical
  filter_upwards [eventually_counted_fourth_row_capacity_shift_late_output (K := K) hd hd8,
    tendsto_twice_nat.eventually (eventually_quadratic_capacity_shift_late (K := K) (d := d) (by omega)),
    tendsto_twice_nat.eventually (eventually_small_quadratic_cross_capacity_shift hd hd8),
    tendsto_twice_nat.eventually (eventually_small_quartic_cross_capacity_shift hd hd8),
    tendsto_twice_nat.eventually (eventually_middle_quartic_diagonal_capacity_shift hd hd8),
    eventually_ge_atTop (72 : ℕ)] with w hfourth hquad hcross₂ hcross₄ hdiag hw
  intro hfour z extra e he
  have hecast : ∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*((2*w : ℕ) : ℝ)^2*(n : ℝ)^(d-2) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using he
  let q := fun n => upperCount (n+z) d
  let counts := fun n => allEvenCount d (2*w) (n+z) (e (n+z)+extra)
  let r := fun n => Fintype.card (Label (q n) (allEvenIndices d) (counts n))
  have hcount : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ))) :=
    allEvenLabel_count_limit_shift (by omega) (2*w) extra z e hecast
  have h4a : 4∈activeEvenIndices d := by
    simp [activeEvenIndices,hd8,show 4<d by omega]
  have hcount4 (n : ℕ) : counts n 4=higherGeneratorCount d (2*w) (n+z) 4 := by
    simp only [counts,allEvenCount_active _ _ _ h4a,targetLayerCount,if_neg (by decide : (4 : ℕ)≠2)]
  have hc₂ : ∀ᶠ n : ℕ in atTop,counts n 2≤
      ⌈countBeta d*((2*w : ℕ) : ℝ)^2*((n+z : ℕ) : ℝ)^(d-2)⌉₊+extra := by
    filter_upwards [(tendsto_add_atTop_nat z).eventually hecast] with n hn
    have hceil : e (n+z)≤⌈countBeta d*((2*w : ℕ) : ℝ)^2*((n+z : ℕ) : ℝ)^(d-2)⌉₊ := by
      exact_mod_cast hn.le.trans (Nat.le_ceil _)
    simpa only [counts,allEvenCount_active _ _ _ (two_mem_activeEvenIndices (d := d) (by omega)),
      targetLayerCount,if_pos rfl,ite_true] using Nat.add_le_add_right hceil extra
  have hq := tendsto_twice_nat.eventually
    (hquad (allEvenIndices d) q counts hcount z extra)
  have hscalar (R : ℕ) (hR : R=6 ∨ R=8) :
      ∀ᶠ v : ℕ in atTop,R≤d → ∀ j,
        ∃ Q : Fin (r (v+v)) → Forms K (v+v) d,
          Function.Injective (ProjectedPrefix.multiplication
            (fun α => MonomialExpansion.partialDegree (balancedScalarHalf v) α≠j) Q (d-R)) := by
    by_cases hRd : R≤d
    · obtain ⟨n₀,hn₀⟩ := eventually_small_single_profile_scalar_open (K := K)
        (by omega : 3≤d) hd8 (Or.inr hR) hRd r hcount
      filter_upwards [eventually_ge_atTop n₀] with v hv
      intro _ j
      obtain ⟨D,⟨Q,hQ⟩,hgood⟩ := hn₀ (v+v) (by omega) (balancedScalarHalf v)
        (by simp only [balancedScalarHalf_card,balancedScalarHalf_compl_card];omega)
        (by simp only [balancedScalarHalf_card,balancedScalarHalf_compl_card];omega) j
      exact ⟨Q,hgood Q hQ⟩
    · exact Eventually.of_forall fun v h => (hRd h).elim
  filter_upwards [hq,hfourth z extra e he,
    tendsto_twice_nat.eventually (hcross₂ z extra),
    tendsto_twice_nat.eventually (hcross₄ z 0),
    tendsto_twice_nat.eventually (hdiag z),
    tendsto_twice_nat.eventually hc₂,hscalar 6 (Or.inl rfl),hscalar 8 (Or.inr rfl),
    eventually_gt_atTop (0 : ℕ)] with v hq0 hfv hc2v hc4v hdv hcv hs6 hs8 hv
  intro X _ _ _ T hX hO hT
  have hqv : QuadraticRowCapacity (v+v) d (q (v+v))
      (fullSparseBlockCount (countBeta d) 2 (d-2) (2*w)) (allEvenIndices d)
      (counts (v+v)) (constrainedOutputs T) := by
    simpa only [two_mul] using hq0 (Fin w × Bool) (constrainedOutputs T) hO hcv
  have hfv' := hfv X T hX hT
  let I := Label (q (v+v)) (allEvenIndices d) (counts (v+v))
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  apply finite_middle_small_witnesses (a := 2*(2*w)/5) (b := 2*w-2*(2*w)/5)
    hd hd8 (by omega) (by simpa only [two_mul] using hfour)
    (by omega) (by omega) hv (by omega) T hT
    (fun j _ hj2 hj4 => allEvenCount_off_two_four_small hd8 _ _ _ hj2 hj4)
    ⟨_,hqv⟩ ⟨_,hfv'⟩
  · simpa only [counts,two_mul,hX,show (v+v)/2=v by omega] using hcv.trans hc2v
  · simpa only [allEvenCount_active _ _ _ h4a,targetLayerCount,
      if_neg (by decide : (4 : ℕ)≠2),Nat.add_zero,two_mul,show (v+v)/2=v by omega] using hc4v
  · by_cases hd5 : d=5
    · simpa only [if_pos hd5,allEvenCount_active _ _ _ h4a,targetLayerCount,
        if_neg (by decide : (4 : ℕ)≠2),two_mul] using hdv
    · simpa only [if_neg hd5,allEvenCount_active _ _ _ h4a,targetLayerCount,
        if_neg (by decide : (4 : ℕ)≠2),two_mul,show (v+v)/2=v by omega] using hdv
  · exact fun h => hs6 h (d-2)
  · exact fun h => hs8 h (2*((d-4)/2))

end Froberg.PreparedParameters
