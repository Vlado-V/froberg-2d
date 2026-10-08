import Quartic.IteratedBlockCharts
import Quartic.LayerRankCounts
import Mathlib.Algebra.Order.Group.Int.Sum
import Mathlib.Order.Interval.Finset.Fin

/-!
# The compressed profile expression bounds genuine chart parameters

The core block is first in the prefix convention. Arbitrary orders of the
three-dimensional blocks are allowed. A sharp subset-position inequality
replaces the sorting argument and yields the manuscript's compressed Cell.
-/

noncomputable section
namespace Quartic.ProfileChartBound
open Module IteratedBlockCharts LayerRankCounts ProfileCertificate FiniteCounts

def blockDimensions (A w : ℕ) : Fin (w+1) → ℕ := Fin.cons A (fun _ => 3)
def blockRanks {w : ℕ} (i : ℕ) (r : Fin w → ℕ) : Fin (w+1) → ℕ := Fin.cons i r

/-- The core-first chart count, before compressing the free-block ranks. -/
theorem parameterCount_blocks {w : ℕ} (A i : ℕ) (r : Fin w → ℕ) :
    parameterCount (blockDimensions A w) (blockRanks i r)=
      i*(A-i)+(∑ l,r l)*(A-i)+(∑ l,r l*(3-r l))+
        ∑ l,∑ k : Fin w,if l < k then r k*(3-r l) else 0 := by
  simp only [parameterCount,blockDimensions,blockRanks,Fin.sum_univ_succ,
    Fin.cons_zero,Fin.cons_succ,Fin.succ_pos,Fin.not_lt_zero,
    Fin.succ_lt_succ_iff,ite_true,ite_false,zero_add]
  rw [Finset.sum_mul]
  ring

/-- The second moment is encoded by the odd weights 1,3,5 on the three layers. -/
theorem rank_square_sum {w : ℕ} (r : Fin w → ℕ) (hr : ∀ l,r l ≤ 3) :
    (∑ l,(r l:ℤ)^2)=
      (levelCount r 1:ℤ)+3*(levelCount r 2:ℤ)+5*(levelCount r 3:ℤ) := by
  classical
  have hp (l : Fin w) : (r l:ℤ)^2=
      (if 1 ≤ r l then 1 else 0)+(if 2 ≤ r l then 3 else 0)+(if 3 ≤ r l then 5 else 0) := by
    have h := hr l
    interval_cases hh : r l <;> norm_num
  simp_rw [hp]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp only [sum_indicator,one_mul,levelCount]

theorem descending_sum_eq (w n : ℕ) :
    (∑ k ∈ Finset.range n,((w:ℤ)-1-k))=(n:ℤ)*w-quadratics n := by
  induction n with
  | zero => simp [quadratics]
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    have h₀ := Counts.b2_scaled n
    have h₁ := Counts.b2_scaled (n+1)
    rw [← quadratics_eq_b2] at h₀ h₁
    push_cast at h₁ ⊢
    nlinarith

/-- Among subsets of a given size, the last positions have the greatest sum. -/
theorem subset_position_sum_bound {w : ℕ} (P : Fin w → Prop) [DecidablePred P] :
    (∑ l : Fin w,if P l then (l.val:ℤ) else 0) ≤
      (Fintype.card {l // P l}:ℤ)*w-quadratics (Fintype.card {l // P l}) := by
  classical
  let s : Finset (Fin w) := Finset.univ.filter P
  let t : Finset ℤ := s.image (fun l => (l.val:ℤ))
  have hinj : Function.Injective (fun l : Fin w => (l.val:ℤ)) := by
    intro x y h
    exact Fin.ext (Int.ofNat_inj.mp h)
  have hcard : t.card=Fintype.card {l // P l} := by
    rw [Finset.card_image_of_injective s hinj]
    exact (Fintype.card_subtype P).symm
  have ht : ∀ z ∈ t,z ≤ (w:ℤ)-1 := by
    intro z hz
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hz
    have hlt := l.isLt
    omega
  have h := Finset.sum_le_sum_range ht
  rw [hcard,descending_sum_eq] at h
  have hsum : (∑ z ∈ t,z)=∑ l : Fin w,if P l then (l.val:ℤ) else 0 := by
    rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
    exact Finset.sum_filter _ _
  rwa [hsum] at h

/-- Weighted positions are maximized by arranging all high-rank blocks last. -/
theorem weighted_position_sum_bound {w : ℕ} (r : Fin w → ℕ) (hr : ∀ l,r l ≤ 3) :
    (∑ l,(l.val:ℤ)*(r l:ℤ)) ≤
      ((levelCount r 1:ℤ)*w-quadratics (levelCount r 1))+
      ((levelCount r 2:ℤ)*w-quadratics (levelCount r 2))+
      ((levelCount r 3:ℤ)*w-quadratics (levelCount r 3)) := by
  classical
  have hp (l : Fin w) : (l.val:ℤ)*(r l:ℤ)=
      (if 1 ≤ r l then (l.val:ℤ) else 0)+(if 2 ≤ r l then (l.val:ℤ) else 0)+
      (if 3 ≤ r l then (l.val:ℤ) else 0) := by
    have h := hr l
    interval_cases hh : r l <;> norm_num <;> ring
  simp_rw [hp]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  exact add_le_add (add_le_add (subset_position_sum_bound (fun l => 1 ≤ r l))
    (subset_position_sum_bound (fun l => 2 ≤ r l))) (subset_position_sum_bound (fun l => 3 ≤ r l))

/-- The sum of pair products is independent of the ordering of the ranks. -/
theorem pair_sum_twice {w : ℕ} (r : Fin w → ℤ) :
    2*(∑ l,∑ k : Fin w,if l < k then r l*r k else 0)=
      (∑ l,r l)^2-∑ l,r l^2 := by
  induction w with
  | zero => simp
  | succ w ih =>
    have h := ih (fun l => r l.succ)
    simp only [Fin.sum_univ_succ,Fin.succ_pos,Fin.not_lt_zero,
      Fin.succ_lt_succ_iff,ite_true,ite_false,zero_add]
    rw [← Finset.mul_sum]
    nlinarith

theorem previous_position_sum {w : ℕ} (l : Fin w) (a : ℤ) :
    (∑ k : Fin w,if k < l then a else 0)=(l.val:ℤ)*a := by
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (fun k : Fin w => k < l)=Finset.Iio l := by ext k; simp
  rw [he,Finset.sum_const,Fin.card_Iio]
  simp

/-- The ordered cross term separates into a weighted position term and an
order-independent pair product. This uses the actual prefix orientation. -/
theorem cross_sum_eq {w : ℕ} (r : Fin w → ℕ) (hr : ∀ l,r l ≤ 3) :
    ((∑ l,∑ k : Fin w,if l < k then r k*(3-r l) else 0 : ℕ):ℤ)=
      3*(∑ l,(l.val:ℤ)*(r l:ℤ))-
        ((∑ l,(r l:ℤ))^2-(∑ l,(r l:ℤ)^2))/2 := by
  classical
  have hp := pair_sum_twice (fun l => (r l:ℤ))
  have hp' : (∑ l,∑ k : Fin w,if l < k then (r l:ℤ)*(r k:ℤ) else 0)=
      ((∑ l,(r l:ℤ))^2-(∑ l,(r l:ℤ)^2))/2 := by omega
  have hfirst : (∑ l,∑ k : Fin w,if l < k then 3*(r k:ℤ) else 0)=
      3*(∑ l,(l.val:ℤ)*(r l:ℤ)) := by
    rw [Finset.sum_comm]
    simp_rw [previous_position_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  calc
    _ = ∑ l,∑ k : Fin w,
        ((if l < k then 3*(r k:ℤ) else 0)-(if l < k then (r l:ℤ)*(r k:ℤ) else 0)) := by
      simp only [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro k _
      split_ifs
      · rw [Nat.cast_mul,Nat.cast_sub (hr l)]
        push_cast
        ring
      · norm_num
    _ = _ := by simp_rw [Finset.sum_sub_distrib]; rw [hfirst,hp']

theorem diagonal_sum_eq {w : ℕ} (r : Fin w → ℕ) (hr : ∀ l,r l ≤ 3) :
    ((∑ l,r l*(3-r l):ℕ):ℤ)=3*(∑ l,(r l:ℤ))-(∑ l,(r l:ℤ)^2) := by
  push_cast
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [Nat.cast_sub (hr l)]
  push_cast
  ring

/-- An exact integer formula for the number of genuine chart parameters. -/
theorem parameterCount_cast {w : ℕ} (A i : ℕ) (hi : i ≤ A)
    (r : Fin w → ℕ) (hr : ∀ l,r l ≤ 3) :
    (parameterCount (blockDimensions A w) (blockRanks i r):ℤ)=
      (i:ℤ)*((A:ℤ)-i)+(∑ l,(r l:ℤ))*((A:ℤ)-i)+
      3*(∑ l,(r l:ℤ))-(∑ l,(r l:ℤ)^2)+
      3*(∑ l,(l.val:ℤ)*(r l:ℤ))-
      ((∑ l,(r l:ℤ))^2-(∑ l,(r l:ℤ)^2))/2 := by
  rw [parameterCount_blocks,Nat.cast_add,Nat.cast_add,Nat.cast_add,
    cross_sum_eq r hr,diagonal_sum_eq r hr]
  push_cast
  rw [Nat.cast_sub hi]
  ring

/-- Every ordering of the free blocks has no more parameters than Cell. -/
theorem parameterCount_le_Cell (m c i : ℕ) (hi : i ≤ coreA c)
    (r : Fin (freeW m c) → ℕ) (hr : ∀ l,r l ≤ 3) :
    (parameterCount (blockDimensions (coreA c) (freeW m c)) (blockRanks i r):ℤ) ≤
      Cell m c i (levelCount r 1) (levelCount r 2) (levelCount r 3) := by
  rw [parameterCount_cast _ _ hi r hr,rank_sum_eq_layers r hr,rank_square_sum r hr]
  have h := weighted_position_sum_bound r hr
  unfold Cell
  dsimp only
  rw [pow_two]
  omega

/-- The actual finite coefficient index of each chart obeys the compressed bound. -/
theorem chart_parameter_card_le_Cell (m c i : ℕ) (hi : i ≤ coreA c)
    (r : Fin (freeW m c) → ℕ) (hr : ∀ l,r l ≤ 3)
    (j : Selectors (blockDimensions (coreA c) (freeW m c)) (blockRanks i r)) :
    (Fintype.card (ParameterIndex j):ℤ) ≤
      Cell m c i (levelCount r 1) (levelCount r 2) (levelCount r 3) := by
  rw [parameter_count]
  exact parameterCount_le_Cell m c i hi r hr

/-- Genuine chart coverage together with the manuscript's compressed parameter bound. -/
theorem exists_chart_with_Cell_bound {K : Type*} [Field K] (m c i : ℕ)
    (r : Fin (freeW m c) → ℕ)
    (S : Submodule K (Ambient K (blockDimensions (coreA c) (freeW m c))))
    (hprofile : ∀ l,finrank K (FilteredImage.initialPiece
      (fun l => Fin (blockDimensions (coreA c) (freeW m c) l) → K) S l)=blockRanks i r l) :
    ∃ j : Selectors (blockDimensions (coreA c) (freeW m c)) (blockRanks i r),
      ∃ p : Parameters K j,chart j p=S ∧ (Fintype.card (ParameterIndex j):ℤ) ≤
        Cell m c i (levelCount r 1) (levelCount r 2) (levelCount r 3) := by
  have hle (l : Fin (freeW m c+1)) : blockRanks i r l ≤ blockDimensions (coreA c) (freeW m c) l := by
    have h := Submodule.finrank_le (FilteredImage.initialPiece
      (fun l => Fin (blockDimensions (coreA c) (freeW m c) l) → K) S l)
    simpa only [hprofile,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using h
  have hi : i ≤ coreA c := hle 0
  have hr : ∀ l,r l ≤ 3 := fun l => hle l.succ
  obtain ⟨j,p,hp⟩ := IteratedBlockCharts.exists_chart S hprofile
  exact ⟨j,p,hp,chart_parameter_card_le_Cell m c i hi r hr j⟩

/-- Unconditional coverage, with the profile extracted from the actual subspace. -/
theorem exists_chart_for_subspace {K : Type*} [Field K] (m c : ℕ)
    (S : Submodule K (Ambient K (blockDimensions (coreA c) (freeW m c)))) :
    let i := finrank K (FilteredImage.initialPiece
      (fun l => Fin (blockDimensions (coreA c) (freeW m c) l) → K) S 0)
    let r := fun l : Fin (freeW m c) => finrank K (FilteredImage.initialPiece
      (fun l => Fin (blockDimensions (coreA c) (freeW m c) l) → K) S l.succ)
    ∃ j : Selectors (blockDimensions (coreA c) (freeW m c)) (blockRanks i r),
      ∃ p : Parameters K j,chart j p=S ∧ (Fintype.card (ParameterIndex j):ℤ) ≤
        Cell m c i (levelCount r 1) (levelCount r 2) (levelCount r 3) := by
  dsimp only
  apply exists_chart_with_Cell_bound
  intro l
  induction l using Fin.cases <;> rfl

end Quartic.ProfileChartBound
