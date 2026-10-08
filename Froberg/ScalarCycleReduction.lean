import Froberg.GradedKoszulElimination

/-! The final algebraic step of coefficient-row elimination. An alternating
matrix of positive components is one actual constant Koszul boundary; the
remaining cycle has only scalar columns. No division by two is used. -/
noncomputable section
namespace Froberg
open Finset
variable {K A I : Type*} [Field K] [CommRing A] [Algebra K A]
variable [Fintype I] [LinearOrder I]

/-- Complete a rectangular positive-column matrix to an alternating matrix,
putting zero in the scalar-scalar block. -/
def alternatingCompletion (P : Finset I) (B : I → I → K) (i j : I) : K :=
  if j∈P then B i j else if i∈P then -B j i else 0

theorem alternatingCompletion_skew (P : Finset I) (B : I → I → K)
    (hB : ∀ i∈P,∀ j∈P,B i j = -B j i) (i j : I) :
    alternatingCompletion P B i j = -alternatingCompletion P B j i := by
  by_cases hi : i∈P <;> by_cases hj : j∈P
  · simpa [alternatingCompletion,hi,hj] using hB i hi j hj
  all_goals simp [alternatingCompletion,hi,hj]

theorem alternatingCompletion_diag (P : Finset I) (B : I → I → K)
    (hB : ∀ i∈P,B i i=0) (i : I) : alternatingCompletion P B i i=0 := by
  by_cases hi : i∈P
  · simp [alternatingCompletion,hi,hB i hi]
  · simp [alternatingCompletion,hi]

/-- The strictly lower half represents an alternating matrix as a boundary. -/
theorem matrixBoundary_lower_of_alternating (q : I → A) (C : I → I → K)
    (hskew : ∀ i j,C i j = -C j i) (hdiag : ∀ i,C i i=0) :
    matrixBoundary q (lowerMatrix C) = matrixCombination q C := by
  funext i
  simp only [matrixBoundary,matrixCombination,Pi.sub_apply,← sum_sub_distrib,← sub_smul]
  apply sum_congr rfl
  intro j hj
  congr 1
  rcases lt_trichotomy i j with h|rfl|h
  · simp [lowerMatrix,h,not_lt_of_ge (le_of_lt h),hskew i j]
  · simp [lowerMatrix,hdiag]
  · simp [lowerMatrix,h,not_lt_of_ge (le_of_lt h)]

/-- If the coefficient rows have the indicated form, a single literal constant
Koszul boundary removes every positive column. The remainder is explicit. -/
theorem scalar_cycle_reduction
    (P : Finset I) (a E b : I → A) (B : I → I → K)
    (hE : ∀ i∉P,E i=0)
    (hzero : ∀ i j,j∉P → B i j=0)
    (hskew : ∀ i∈P,∀ j∈P,B i j = -B j i)
    (hdiag : ∀ i∈P,B i i=0)
    (hb : ∀ j∈P,b j = -∑ i,B i j • a i) :
    (fun i => b i + matrixCombination E B i) -
        matrixBoundary (fun i => a i+E i) (lowerMatrix (alternatingCompletion P B)) =
      fun i => if i∈P then 0 else b i-∑ j∈P,B i j • a j := by
  rw [matrixBoundary_lower_of_alternating _ _
    (alternatingCompletion_skew P B hskew) (alternatingCompletion_diag P B hdiag)]
  funext i
  simp only [Pi.sub_apply,matrixCombination]
  by_cases hi : i∈P
  · rw [if_pos hi,hb i hi]
    have hC (j : I) : alternatingCompletion P B i j = -B j i := by
      by_cases hj : j∈P
      · simpa [alternatingCompletion,hj] using hskew i hi j hj
      · simp [alternatingCompletion,hi,hj]
    simp_rw [hC,neg_smul,smul_add]
    rw [sum_neg_distrib,sum_add_distrib]
    have hs : ∑ j,B i j • E j = -∑ j,B j i • E j := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro j hj
      by_cases hjP : j∈P
      · rw [hskew i hi j hjP,neg_smul]
      · simp [hE j hjP]
    rw [hs]
    abel
  · rw [if_neg hi]
    have hC (j : I) : alternatingCompletion P B i j = B i j := by
      by_cases hj : j∈P
      · simp [alternatingCompletion,hj]
      · simp [alternatingCompletion,hi,hj,hzero i j hj]
    simp_rw [hC,smul_add]
    rw [sum_add_distrib]
    have hs : ∑ j,B i j • a j = ∑ j∈P,B i j • a j := by
      apply (sum_subset (subset_univ P) ?_).symm
      intro j hj hjP
      simp [hzero i j hjP]
    rw [hs]
    abel

/-- The scalar remainder is itself a relation whenever the original vector
was a relation. -/
theorem scalar_remainder_cycle
    (P : Finset I) (a E b : I → A) (B : I → I → K)
    (hE : ∀ i∉P,E i=0)
    (hzero : ∀ i j,j∉P → B i j=0)
    (hskew : ∀ i∈P,∀ j∈P,B i j = -B j i)
    (hdiag : ∀ i∈P,B i i=0)
    (hb : ∀ j∈P,b j = -∑ i,B i j • a i)
    (hcycle : ∑ i,(a i+E i)*(b i+matrixCombination E B i)=0) :
    ∑ i∈Pᶜ,a i*(b i-∑ j∈P,B i j • a j)=0 := by
  have heq := scalar_cycle_reduction P a E b B hE hzero hskew hdiag hb
  have hc : ∑ i,(a i+E i)*
      ((fun k => b k+matrixCombination E B k) -
        matrixBoundary (fun k => a k+E k) (lowerMatrix (alternatingCompletion P B))) i=0 := by
    simp only [Pi.sub_apply,mul_sub,sum_sub_distrib,hcycle,matrixBoundary_cycle,sub_self]
  rw [heq] at hc
  have hc' : (∑ i,if i∈Pᶜ then a i*(b i-∑ j∈P,B i j • a j) else 0)=0 := by
    convert hc using 1
    apply sum_congr rfl
    intro i hi
    by_cases hiP : i∈P
    · simp [hiP]
    · simp [hiP,hE i hiP]
  simpa only [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter] using hc'

end Froberg
