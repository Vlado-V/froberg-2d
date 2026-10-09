module

public import Froberg.PreparedMiddleSmallReduction
public import Froberg.CountedFourthRow

@[expose] public section

/-! The exact rounded counts, with a fixed private-variable reserve and
fixed appended columns, satisfy every finite small-degree witness bound. -/
noncomputable section
set_option maxHeartbeats 2200000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

theorem allEvenCount_off_two_four_small {d : ℕ} (hd8 : d≤8)
    (h n e : ℕ) {j : ℕ} (hj2 : j≠2) (hj4 : j≠4) : allEvenCount d h n e j=0 := by
  apply allEvenCount_inactive
  simp only [activeEvenIndices,if_pos hd8,Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
  tauto

theorem eventually_middle_quartic_diagonal_capacity_shift {d : ℕ} (hd : 5≤d) (hd8 : d≤8) :
    ∀ᶠ h : ℕ in atTop,∀ z : ℕ,∀ᶠ n : ℕ in atTop,
      higherGeneratorCount d h (n+z) 4≤
        if d=5 then (h^4/256)*(n/2) else (h^4/256)*((n/2).choose (d-4)/2) := by
  by_cases hd5 : d=5
  · subst d
    filter_upwards [eventually_quintic_quartic_diagonal_capacity_shift] with h hh
    intro z
    simpa only [if_pos rfl,ite_true,Nat.add_zero] using hh z 0
  · filter_upwards [eventually_small_quartic_diagonal_capacity_shift (by omega) hd8] with h hh
    intro z
    simpa only [if_neg hd5,Nat.add_zero] using hh z 0

theorem eventually_actual_middle_small_witnesses_shift_uniform {d : ℕ}
    (hd : 5≤d) (hd8 : d≤8) :
    ∀ᶠ w : ℕ in atTop,4∣2*w →
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) →
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) →
      T 4=0 → ∀ (z extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ v : ℕ in atTop,
        let A := Space (v+v) d (upperCount (v+v+z) d) (allEvenIndices d)
          (allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)) (constrainedOutputs T)
        (∀ R : allEvenIndices d,∃ p : A,
          LinearIndependent K (fun i => intrinsicLayerMap (fun _ _ => inf_le_left) R i p) ∧
          (row (fun _ _ => inf_le_left) R p).ker=(rowConstants (fun _ _ => inf_le_left) R p).range) ∧
        (∀ R,d<R → R≤2*d → R%2=0 → ∃ p : A,
          Function.Injective (ProductRows.multiplication
            (allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)) (layers p) (allEvenIndices d) R)) := by
  classical
  filter_upwards [eventually_counted_fourth_row_capacity_shift_uniform (K := K) hd hd8,
    tendsto_twice_nat.eventually (eventually_quadratic_capacity_shift (K := K) (d := d) (by omega)),
    tendsto_twice_nat.eventually (eventually_small_quadratic_cross_capacity_shift hd hd8),
    tendsto_twice_nat.eventually (eventually_small_quartic_cross_capacity_shift hd hd8),
    tendsto_twice_nat.eventually (eventually_middle_quartic_diagonal_capacity_shift hd hd8),
    eventually_ge_atTop (72 : ℕ)] with w hfourth hquad hcross₂ hcross₄ hdiag hw
  intro hfour X _ _ _ T hX hO hT z extra e he
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
  have hq : ∀ᶠ v : ℕ in atTop,QuadraticRowCapacity (v+v) d (q (v+v))
      (fullSparseBlockCount (countBeta d) 2 (d-2) (2*w)) (allEvenIndices d)
      (counts (v+v)) (constrainedOutputs T) := by
    filter_upwards [tendsto_twice_nat.eventually
      (hquad (Fin w × Bool) (constrainedOutputs T) hO (allEvenIndices d) q counts hcount z extra),
      tendsto_twice_nat.eventually hc₂] with v hv hc
    simpa only [two_mul] using hv hc
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
  filter_upwards [hq,hfourth X T hX hT z extra e he,
    tendsto_twice_nat.eventually (hcross₂ z extra),
    tendsto_twice_nat.eventually (hcross₄ z 0),
    tendsto_twice_nat.eventually (hdiag z),
    tendsto_twice_nat.eventually hc₂,hscalar 6 (Or.inl rfl),hscalar 8 (Or.inr rfl),
    eventually_gt_atTop (0 : ℕ)] with v hqv hfv hc2v hc4v hdv hcv hs6 hs8 hv
  let I := Label (q (v+v)) (allEvenIndices d) (counts (v+v))
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  apply finite_middle_small_witnesses (a := 2*(2*w)/5) (b := 2*w-2*(2*w)/5)
    hd hd8 (by omega) (by simpa only [two_mul] using hfour)
    (by omega) (by omega) hv (by omega) T hT
    (fun j _ hj2 hj4 => allEvenCount_off_two_four_small hd8 _ _ _ hj2 hj4)
    ⟨_,hqv⟩ ⟨_,hfv⟩
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

theorem eventually_actual_middle_small_reduction_open_shift_uniform {d : ℕ}
    (hd : 5≤d) (hd8 : d≤8) :
    ∀ᶠ w : ℕ in atTop,4∣2*w →
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) →
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) →
      T 4=0 → ∀ (z extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ v : ℕ in atTop,
        let A := Space (v+v) d (upperCount (v+v+z) d) (allEvenIndices d)
          (allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)) (constrainedOutputs T)
        ∃ D : MvPolynomial (Fin (finrank K A)) K,
          (∃ p : A,eval ((Module.finBasis K A).equivFun p) D≠0) ∧
          ∀ p : A,eval ((Module.finBasis K A).equivFun p) D≠0 → EvenPositiveReduction p := by
  classical
  filter_upwards [eventually_actual_middle_small_witnesses_shift_uniform (K := K) hd hd8] with w hw
  intro hfour X _ _ _ T hX hO hT z extra e he
  filter_upwards [hw hfour X T hX hO hT z extra e he] with v hv
  let I := Label (upperCount (v+v+z) d) (allEvenIndices d)
    (allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra))
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  exact even_reduction_open_of_witnesses (fun _ _ => inf_le_left)
    (fun _ hj => (mem_allEvenIndices.mp hj).1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.2)
    (fun r hr hrd hre => mem_allEvenIndices.mpr ⟨by omega,hrd,hre⟩)
    hv.1 hv.2

end Froberg.PreparedParameters
