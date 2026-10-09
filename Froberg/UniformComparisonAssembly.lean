module

public import Froberg.SelectedBlockParameters
public import Froberg.CriticalComparisonCounts
public import Froberg.EndpointFieldDescent
public import Froberg.UniformStatement
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

/-! Assemble a common geometric recurrence from comparison blocks whose
cutoffs precede the choice of field. The numerical block and both count
sequences are selected once, and descent preserves the resulting cutoff. -/
noncomputable section
namespace Froberg
open Filter

def UniformCriticalComparisonBlock (d h : ℕ) : Prop :=
  4∣h → ∀ (k lo : ℕ),0<k → h=k*centralHalfBinomial d → 0<h →
    ∀ (upper : Bool) (a f e : ℕ → ℕ),(∀ n,a n≤n) →
    (∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) →
    ∀ δ : ℝ,0<δ →
    (∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) →
    ∀ᶠ n : ℕ in atTop,∀ (K : Type) [Field K] [Infinite K] [IsAlgClosed K],
      Nonempty (LocalComparisonData K (h+n) d
        (adjacentCriticalCount upper (h+n) d) (criticalDefect K n d))

theorem uniformCriticalRecurrence_of_comparison_blocks {d : ℕ} (hd : 3≤d)
    (hblocks : ∀ᶠ w : ℕ in atTop,UniformCriticalComparisonBlock d (2*w)) :
    UniformCriticalRecurrence d := by
  classical
  obtain ⟨k,w,hblock,hdiv,hcompare,δ,a,f,e,hδ,ha,hcounts⟩ :=
    exact_count_sequences_with_block_property hd 1 (UniformCriticalComparisonBlock d) hblocks
  have hfor (upper : Bool) : ∀ᶠ n : ℕ in atTop,
      ∀ (K : Type) [Field K] [Infinite K] [IsAlgClosed K],
      Nonempty (LocalComparisonData K (2*w+n) d
        (adjacentCriticalCount upper (2*w+n) d) (criticalDefect K n d)) := by
    apply hcompare hdiv k 1 hblock.multiplicity_pos hblock.size_eq hblock.size_pos
      upper (a upper) (f upper) (e upper) (ha upper)
      (hcounts.mono fun n hn => (hn upper).1) δ hδ
    exact hcounts.mono fun n hn => (hn upper).2
  have hboth : ∀ᶠ n : ℕ in atTop,0<n ∧
      ∀ (K : Type) [Field K] [Infinite K] [IsAlgClosed K],
      criticalDefect K (n+2*w) d≤criticalDefect K n d := by
    filter_upwards [hfor false,hfor true,eventually_gt_atTop (0 : ℕ)] with n hf ht hn
    refine ⟨hn,?_⟩
    intro K _ _ _
    apply criticalDefect_step_of_comparison_data hn
    intro upper
    cases upper
    · simpa only [Nat.add_comm n] using Classical.choice (hf K)
    · simpa only [Nat.add_comm n] using Classical.choice (ht K)
  obtain ⟨start,hstart⟩ := eventually_atTop.mp hboth
  refine ⟨2*w,start,hblock.size_pos,?_⟩
  intro K _ _ n hn
  obtain ⟨hnpos,hrec⟩ := hstart n hn
  rw [criticalDefect_baseChange (algebraMap K (AlgebraicClosure K)) (by omega : 0<n+2*w),
    criticalDefect_baseChange (algebraMap K (AlgebraicClosure K)) hnpos]
  exact hrec (AlgebraicClosure K)

end Froberg
