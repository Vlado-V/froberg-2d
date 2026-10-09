module

public import Froberg.Koszul
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Elementary coefficient operations used in increasing-degree elimination.
The triangular representative works in every characteristic, including two. -/
noncomputable section
namespace Froberg
open Finset
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
variable {I : Type*} [Fintype I]

def matrixCombination (q : I → A) (C : I → I → K) : I → A :=
  fun i => ∑ j, C i j • q j

def matrixBoundary (q : I → A) (C : I → I → K) : I → A :=
  matrixCombination q C - matrixCombination q (fun i j => C j i)

/-- Every matrix operation below is a sum of literal constant Koszul boundaries. -/
theorem matrixBoundary_cycle (q : I → A) (C : I → I → K) :
    ∑ i, q i * matrixBoundary q C i = 0 := by
  simp only [matrixBoundary,matrixCombination,Pi.sub_apply,mul_sub,mul_sum,
    mul_smul_comm,Finset.sum_sub_distrib]
  apply sub_eq_zero.mpr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm]

/-- If both columns of every used boundary have no component in a previously
processed degree, the boundary operation preserves that degree exactly. -/
theorem matrixBoundary_component_zero
    (q : I → A) (C : I → I → K) (P : A →ₗ[K] A)
    (hP : ∀ i j, C i j≠0 → P (q i)=0 ∧ P (q j)=0) (i : I) :
    P (matrixBoundary q C i)=0 := by
  simp only [matrixBoundary,matrixCombination,Pi.sub_apply,map_sub,map_sum,map_smul]
  have hleft : ∑ j, C i j • P (q j)=0 := by
    apply sum_eq_zero
    intro j hj
    by_cases hc : C i j=0
    · simp [hc]
    · rw [(hP i j hc).2,smul_zero]
  have hright : ∑ j, C j i • P (q j)=0 := by
    apply sum_eq_zero
    intro j hj
    by_cases hc : C j i=0
    · simp [hc]
    · rw [(hP j i hc).1,smul_zero]
  rw [hleft,hright,sub_self]

section Ordered
variable [LinearOrder I]

/-- Keep the diagonal and put the two off-diagonal coefficients in the upper
triangle. No division by two is used. -/
def upperMatrix (C : I → I → K) (i j : I) : K :=
  if i < j then C i j+C j i else if i=j then C i j else 0

def lowerMatrix (C : I → I → K) (i j : I) : K := if j < i then C i j else 0

theorem matrix_sub_upper (C : I → I → K) (i j : I) :
    C i j-upperMatrix C i j=lowerMatrix C i j-lowerMatrix C j i := by
  rcases lt_trichotomy i j with h|rfl|h
  · simp [upperMatrix,lowerMatrix,h,not_lt_of_ge (le_of_lt h),ne_of_lt h]
  · simp [upperMatrix,lowerMatrix]
  · simp [upperMatrix,lowerMatrix,h,not_lt_of_ge (le_of_lt h),ne_of_gt h]

/-- Every coefficient matrix is congruent modulo constant Koszul boundaries
to its upper-triangular representative. -/
theorem matrixCombination_sub_upper (q : I → A) (C : I → I → K) :
    matrixCombination q C-matrixCombination q (upperMatrix C)=
      matrixBoundary q (lowerMatrix C) := by
  funext i
  simp only [matrixBoundary,matrixCombination,Pi.sub_apply,← Finset.sum_sub_distrib,
    ← sub_smul,matrix_sub_upper]

/-- A triangular representative gives exactly the same polynomial product. -/
theorem matrixCombination_upper_same_product (q : I → A) (C : I → I → K) :
    ∑ i,q i*matrixCombination q C i = ∑ i,q i*matrixCombination q (upperMatrix C) i := by
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  change (∑ i,q i*(matrixCombination q C-matrixCombination q (upperMatrix C)) i)=0
  rw [matrixCombination_sub_upper]
  exact matrixBoundary_cycle q (lowerMatrix C)

/-- Previously processed components are unchanged by the normalization. -/
theorem upper_normalization_preserves_component
    (q : I → A) (C : I → I → K) (P : A →ₗ[K] A)
    (hP : ∀ i j,j < i → C i j≠0 → P (q i)=0 ∧ P (q j)=0) (i : I) :
    P (matrixCombination q C i)=P (matrixCombination q (upperMatrix C) i) := by
  have hz := matrixBoundary_component_zero q (lowerMatrix C) P (by
    intro a b hab
    have hba : b < a := by by_contra h; simp [lowerMatrix,h] at hab
    have hc : C a b≠0 := by simpa [lowerMatrix,hba] using hab
    exact hP a b hba hc) i
  rw [← matrixCombination_sub_upper] at hz
  simpa only [Pi.sub_apply,map_sub,sub_eq_zero] using hz

end Ordered
end Froberg
