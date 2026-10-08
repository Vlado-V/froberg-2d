import Froberg.PreparedAllEvenProducts
import Froberg.ActualQuadraticCapacity
import Froberg.EmptyHigherCapacity
import Froberg.OddOutputLimit

/-! Actual rounded Section 5 counts satisfy all finite even-row records on
one common range of variable counts. No asymptotic capacity is left as an
extra hypothesis; the quadratic output space has its prescribed dimension. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
open scoped Topology
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem oddOutputDimension_eventually_positive {R : ℕ} (hR : 0<R) :
    ∀ᶠ w : ℕ in atTop,0<oddOutputDimension w R := by
  have hp : (0:ℝ)<2^(R-1)/(R.factorial : ℝ) := by positivity
  filter_upwards [(oddOutputDimension_normalized_limit hR).eventually (eventually_gt_nhds hp)] with w hw
  apply Nat.pos_of_ne_zero
  intro hz
  simpa only [hz,Nat.cast_zero,zero_div,lt_self_iff_false] using hw

theorem eventually_actual_even_capacities {d : ℕ} (hd : 9≤d) :
    ∀ᶠ w : ℕ in atTop,
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) →
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) →
      (∀ R,4≤R → T R=0) →
      ∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ v : ℕ in atTop,
        (∃ b,QuadraticRowCapacity (v+v) d (upperCount (v+v) d) b (allEvenIndices d)
          (allEvenCount d (2*w) (v+v) (e (v+v)+extra)) (constrainedOutputs T)) ∧
        (∀ R : allEvenIndices d,R.val≠2 → ∃ b,HigherRowCapacity w v d (upperCount (v+v) d) b
          (allEvenIndices d) (allEvenCount d (2*w) (v+v) (e (v+v)+extra)) T R) ∧
        ∀ R,ProductRowCapacity (K := K) (X := X) w v d R (allEvenIndices d)
          (allEvenCount d (2*w) (v+v) (e (v+v)+extra)) := by
  have hhigh : ∀ᶠ w : ℕ in atTop,∀ R : activeHigherIndices d,
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) → T R.val=0 →
      ∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ v : ℕ in atTop,HigherRowCapacity w v d (upperCount (v+v) d)
        (sparseBlockCount ((101/100:ℝ)*higherCountGamma d R.val) R.val (d-R.val) w)
        (activeEvenIndices d) (targetLayerCount d (2*w) (v+v) (e (v+v)+extra)) T
        ⟨R.val,(Finset.mem_filter.mp R.property).1⟩ :=
    eventually_all.mpr fun R => eventually_higher_row_capacity (K := K) (X := X) hd R.property
  have hpos : ∀ᶠ w : ℕ in atTop,∀ R : allEvenIndices d,0<oddOutputDimension w R.val :=
    eventually_all.mpr fun R => oddOutputDimension_eventually_positive
      (by have := (mem_allEvenIndices.mp R.property).1;omega)
  filter_upwards [hhigh,hpos,eventually_allEven_product_capacities (K := K) (X := X) hd,
    tendsto_twice_nat.eventually (eventually_actual_quadratic_capacity (K := K) (by omega : 3≤d))]
    with w hhigher hpos hproduct hquadratic
  intro T hX hO hT extra e he
  have hecast : ∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*((2*w : ℕ):ℝ)^2*(n:ℝ)^(d-2) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using he
  have hcount := allEvenLabel_count_limit (by omega : 3≤d) (2*w) extra e hecast
  have hp : ∀ᶠ v : ℕ in atTop,∀ R,ProductRowCapacity (K := K) (X := X) w v d R (allEvenIndices d)
      (allEvenCount d (2*w) (v+v) (e (v+v)+extra)) := by
    filter_upwards [hproduct extra,tendsto_twice_nat.eventually he] with v hv hev
    simpa only [two_mul] using hv (e (2*v))
      (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hev) hX
  have hq := tendsto_twice_nat.eventually
    (hquadratic (Fin w × Bool) (constrainedOutputs T) hO extra e hecast)
  have hRcap (R : allEvenIndices d) (hR2 : R.val≠2) :
      ∀ᶠ v : ℕ in atTop,∃ b,HigherRowCapacity w v d (upperCount (v+v) d) b (allEvenIndices d)
        (allEvenCount d (2*w) (v+v) (e (v+v)+extra)) T R := by
    obtain ⟨hRlow,hRd,hRe⟩ := mem_allEvenIndices.mp R.property
    have hR4 : 4≤R.val := by omega
    by_cases ha : R.val∈activeEvenIndices d
    · have hRa : R.val∈activeHigherIndices d := Finset.mem_filter.mpr ⟨ha,hR4⟩
      filter_upwards [hhigher ⟨R.val,hRa⟩ T hX (hT _ hR4) extra e he,hp] with v hv hpv
      refine ⟨_,hv.with_labels rfl (allEvenLabel_card (by omega) _ _ _ _) ?_ (hpv R.val)
        (fun j hj => by have := (mem_allEvenIndices.mp hj).1;omega)⟩
      exact allEvenCount_active _ _ _ ha
    · have hempty := eventually_empty_higher_capacity (K := K) (X := X) hd (allEvenIndices d) R hR4 hRd
        T (hT _ hR4) (hpos R) (fun n => upperCount n d)
        (fun n => allEvenCount d (2*w) n (e n+extra))
        (fun n => allEvenCount_inactive _ _ _ ha) hcount
      filter_upwards [hempty,hp] with v hv hpv
      exact ⟨0,hv (hpv R.val) (fun j hj => by have := (mem_allEvenIndices.mp hj).1;omega)⟩
  filter_upwards [hq,hp,eventually_all.mpr (fun R : {R : allEvenIndices d // R.val≠2} =>
    hRcap R.val R.property)] with v hqv hpv hRv
  refine ⟨⟨fullSparseBlockCount (countBeta d) 2 (d-2) (2*w),?_⟩,
    (fun R hR => hRv ⟨R,hR⟩),hpv⟩
  have hqa : QuadraticRowCapacity (v+v) d (upperCount (v+v) d)
      (fullSparseBlockCount (countBeta d) 2 (d-2) (2*w)) (activeEvenIndices d)
      (targetLayerCount d (2*w) (v+v) (e (v+v)+extra)) (constrainedOutputs T) := by
    simpa only [two_mul] using hqv
  apply hqa.with_labels (allEvenLabel_card (by omega) _ _ _ _)
  exact allEvenCount_active _ _ _ (two_mem_activeEvenIndices (by omega))

end Froberg.PreparedParameters
