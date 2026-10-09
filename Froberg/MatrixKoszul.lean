module

public import Froberg.GradedKoszulElimination

@[expose] public section

/-! Matrix boundaries are elements of the ordinary incoming Koszul span. -/
noncomputable section
namespace Froberg
open Finset
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] {r : ℕ}

def orderedPairVector (q : Fin r → A) (i j : Fin r) : Fin r → A :=
  fun k => (if k=i then q j else 0)-(if k=j then q i else 0)

theorem orderedPairVector_mem_koszul (q : Fin r → A) (i j : Fin r) :
    orderedPairVector q i j∈Submodule.span K (Set.range (koszulVector q)) := by
  classical
  rcases lt_trichotomy i j with h|rfl|h
  · exact Submodule.subset_span ⟨⟨(i,j),h⟩,rfl⟩
  · have hz : orderedPairVector q i i=0 := by funext k; simp [orderedPairVector]
    rw [hz]
    exact Submodule.zero_mem _
  · have hn : orderedPairVector q i j = -koszulVector q ⟨(j,i),h⟩ := by
      funext k
      simp only [orderedPairVector,koszulVector,Pi.neg_apply,neg_sub]
    rw [hn]
    exact Submodule.neg_mem _ (Submodule.subset_span ⟨⟨(j,i),h⟩,rfl⟩)

theorem matrixBoundary_eq_sum_pairs (q : Fin r → A) (C : Fin r → Fin r → K) :
    matrixBoundary q C=∑ i,∑ j,C i j • orderedPairVector q i j := by
  classical
  funext k
  simp only [matrixBoundary,matrixCombination,Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,
    orderedPairVector,smul_sub,smul_ite,smul_zero,sum_sub_distrib]
  congr 1
  · rw [sum_comm]
    simp
  · simp

theorem matrixBoundary_mem_koszul (q : Fin r → A) (C : Fin r → Fin r → K) :
    matrixBoundary q C∈Submodule.span K (Set.range (koszulVector q)) := by
  rw [matrixBoundary_eq_sum_pairs]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _ (orderedPairVector_mem_koszul q i j)

end Froberg
