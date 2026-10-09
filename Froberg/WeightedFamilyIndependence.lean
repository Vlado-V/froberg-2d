module

public import Froberg.FilteredFamilyIndependence
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

@[expose] public section

/-! Separate positive weights detect all coefficients of a finite family. -/
noncomputable section
namespace Froberg
open MvPolynomial
variable {K σ : Type*} [Field K] {w : σ → ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}

theorem weighted_family_independent
    (g : (j : J) → Fin (counts j.val) → MvPolynomial σ K)
    (hw : ∀ j i,(g j i).IsWeightedHomogeneous w j.val)
    (hg : ∀ j,LinearIndependent K (g j)) :
    LinearIndependent K (fun i : Σ j : J,Fin (counts j.val) => g i.1 i.2) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hcomp (j : J) (k : Fin (counts j.val)) :
      weightedHomogeneousComponent w i.1.val (g j k)=if j=i.1 then g j k else 0 := by
    rw [weightedHomogeneousComponent_of_mem (hw j k)]
    by_cases hj : j=i.1
    · subst j
      simp
    · have hv : i.1.val≠j.val := fun h => hj (Subtype.ext h.symm)
      rw [if_neg hv,if_neg hj]
  have hrel := congrArg (weightedHomogeneousComponent w i.1.val) hc
  simp only [map_sum,map_smul,map_zero,Fintype.sum_sigma,hcomp] at hrel
  have hi : (∑ k,c ⟨i.1,k⟩ • g i.1 k)=0 := by
    simpa [smul_ite] using hrel
  exact Fintype.linearIndependent_iff.mp (hg i.1) _ hi i.2

end Froberg
