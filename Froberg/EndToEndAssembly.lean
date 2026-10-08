import Froberg.ActualPreparedComparison
import Froberg.ActualRestoredComparison
import Froberg.CountedPreparedSelection
import Froberg.SelectedBlockParameters
import Froberg.AlgebraicClosureAssembly

/-! The actual odd and even constructions give comparisons at both adjacent
critical generator counts.  A common block size then gives the defect
recurrence, and the arithmetic vanishing theorem completes the endpoint
and Hilbert-function statements over every characteristic-zero field. -/
noncomputable section
set_option maxHeartbeats 900000
namespace Froberg
open Filter PreparedParameters PreparedTarget

private theorem tendsto_double_atTop :
    Tendsto (fun w : ℕ => 2*w) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with w hw
  omega

/-- The comparison property of one fixed output block, uniform over the
exact-count sequences for either adjacent critical count. -/
def CriticalComparisonBlock (K : Type) [Field K] [Infinite K] (d h : ℕ) : Prop :=
  4∣h → ∀ (k lo : ℕ),0<k → h=k*centralHalfBinomial d → 0<h →
    ∀ (upper : Bool) (a f e : ℕ → ℕ),(∀ n,a n≤n) →
    (∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) →
    ∀ δ : ℝ,0<δ →
    (∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) →
    ∀ᶠ n : ℕ in atTop,Nonempty (LocalComparisonData K (h+n) d
      (adjacentCriticalCount upper (h+n) d) (criticalDefect K n d))

section AlgebraicallyClosed
variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K]

theorem eventually_criticalComparisonBlock {d : ℕ} (hd : 3≤d) :
    ∀ᶠ w : ℕ in atTop,CriticalComparisonBlock K d (2*w) := by
  by_cases he : d%2=0
  · filter_upwards [tendsto_double_atTop.eventually
      (eventually_counted_restored_frame_ready (K := K) hd he)] with w hw
    intro hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres
    exact actual_restored_comparison_of_eventual_frames hd he hk hkh hhpos
      upper a f e ha hc hδ hres (hw hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres)
  · have ho : d%2=1 := by omega
    have hodd : Odd d := Nat.odd_iff.mpr ho
    filter_upwards [eventually_counted_prepared_frame_ready (K := K) hd ho,
      tendsto_double_atTop.eventually
        (eventually_odd_pure_projection_data (K := K) hd hodd)] with w hw hpure
    obtain ⟨pure⟩ := hpure
    intro hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres
    have hframes := hw hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres
      (tailGeneratorCount d (2*w))
    have hcomparison := eventually_actual_prepared_comparison (K := K) hd ho hk hkh hhpos
      pure upper a f e ha hc hδ hres
    filter_upwards [hframes,hcomparison] with n hfn hcn
    obtain ⟨frame,hframe⟩ := hfn pure.U
      (PreparedTarget.OddPureProjectionData.admissible pure hodd)
    exact hcn (targetLayerOutput frame)
      (fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j)
      hframe.base _ (Fintype.equivFin _).symm hframe.enlarged

/-- Both adjacent critical counts satisfy the same eventual defect recurrence. -/
theorem actual_critical_defect_recurrence {d : ℕ} (hd : 3≤d) :
    ∃ h start : ℕ,0<h ∧ ∀ n,start≤n → criticalDefect K (n+h) d≤criticalDefect K n d := by
  obtain ⟨k,w,hblock,hdiv,hcompare,δ,a,f,e,hδ,ha,hcounts⟩ :=
    exact_count_sequences_with_block_property hd 1 (CriticalComparisonBlock K d)
      (eventually_criticalComparisonBlock (K := K) hd)
  have hfor (upper : Bool) : ∀ᶠ n : ℕ in atTop,
      Nonempty (LocalComparisonData K (2*w+n) d
        (adjacentCriticalCount upper (2*w+n) d) (criticalDefect K n d)) := by
    apply hcompare hdiv k 1 hblock.multiplicity_pos hblock.size_eq hblock.size_pos
      upper (a upper) (f upper) (e upper) (ha upper)
      (hcounts.mono fun n hn => (hn upper).1) δ hδ
    exact hcounts.mono fun n hn => (hn upper).2
  have hboth : ∀ᶠ n : ℕ in atTop,∀ upper : Bool,
      Nonempty (LocalComparisonData K (2*w+n) d
        (adjacentCriticalCount upper (2*w+n) d) (criticalDefect K n d)) := by
    filter_upwards [hfor false,hfor true] with n hf ht
    intro upper
    cases upper <;> assumption
  obtain ⟨start,hstart⟩ := eventual_recurrence_of_core_first_comparison hboth
  exact ⟨2*w,start,hblock.size_pos,hstart⟩

end AlgebraicallyClosed

/-- Fröberg's predicted Hilbert function through degree `2*d`, for every
fixed positive generating degree and all sufficiently many variables. -/
theorem mainStatement (K : Type) [Field K] [CharZero K] : MainStatement K := by
  apply mainStatement_of_algClosed_inductive_recurrence
  -- The direct row-two convolution construction proves the recurrence without
  -- using the preceding-degree induction hypothesis.
  intro L _ _ _ d hd _
  exact actual_critical_defect_recurrence (K := L) hd

end Froberg
