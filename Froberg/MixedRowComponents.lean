module

public import Froberg.LowHomogeneousProduct

@[expose] public section

/-! Exact coefficient rows for scalar-plus-positive-degree generators. -/
noncomputable section
namespace Froberg
open MvPolynomial Finset
variable {K σ I : Type*} [Field K] [Fintype I]

/-- Multiplication by a homogeneous factor shifts the weighted component by
exactly its degree; no negative-degree component is introduced. -/
theorem weightedComponent_homogeneous_left (w : σ → ℕ)
    {p : MvPolynomial σ K} {j : ℕ} (hp : p.IsWeightedHomogeneous w j)
    (q : MvPolynomial σ K) (r : ℕ) :
    weightedHomogeneousComponent w r (p*q) =
      if j≤r then p*weightedHomogeneousComponent w (r-j) q else 0 := by
  classical
  rw [weightedHomogeneousComponent_product]
  by_cases hj : j≤r
  · rw [if_pos hj]
    have hmem : (j,r-j)∈antidiagonal r := mem_antidiagonal.mpr (Nat.add_sub_of_le hj)
    rw [sum_eq_single (j,r-j)]
    · simp [weightedHomogeneousComponent_of_mem hp]
    · intro b hb hbj
      have hb' := mem_antidiagonal.mp hb
      have hne : j≠b.1 := by
        intro h
        apply hbj
        apply Prod.ext
        · exact h.symm
        · omega
      simp [weightedHomogeneousComponent_of_mem hp,hne,Ne.symm hne]
    · exact fun h => False.elim (h hmem)
  · rw [if_neg hj]
    apply sum_eq_zero
    intro b hb
    have hb' := mem_antidiagonal.mp hb
    have hne : j≠b.1 := by omega
    simp [weightedHomogeneousComponent_of_mem hp,hne,Ne.symm hne]

/-- The literal row of a polynomial relation among scalar-plus-homogeneous
columns. This is the coefficient identity used in B.5's increasing-row induction. -/
theorem mixed_generator_component_row (w : σ → ℕ)
    (a E c : I → MvPolynomial σ K) (j : I → ℕ)
    (ha : ∀ i,(a i).IsWeightedHomogeneous w 0)
    (hE : ∀ i,(E i).IsWeightedHomogeneous w (j i)) (r : ℕ) :
    weightedHomogeneousComponent w r (∑ i,(a i+E i)*c i) =
      (∑ i,a i*weightedHomogeneousComponent w r (c i)) +
      ∑ i,if j i≤r then E i*weightedHomogeneousComponent w (r-j i) (c i) else 0 := by
  simp only [map_sum,add_mul,map_add,Finset.sum_add_distrib,
    weightedComponent_homogeneous_left w (ha _),Nat.zero_le,Nat.sub_zero,if_true,
    weightedComponent_homogeneous_left w (hE _)]

/-- Every actual cycle satisfies the displayed row equation in every degree. -/
theorem mixed_cycle_row (w : σ → ℕ)
    (a E c : I → MvPolynomial σ K) (j : I → ℕ)
    (ha : ∀ i,(a i).IsWeightedHomogeneous w 0)
    (hE : ∀ i,(E i).IsWeightedHomogeneous w (j i))
    (hc : ∑ i,(a i+E i)*c i=0) (r : ℕ) :
    (∑ i,a i*weightedHomogeneousComponent w r (c i)) +
      (∑ i,if j i≤r then E i*weightedHomogeneousComponent w (r-j i) (c i) else 0)=0 := by
  rw [← mixed_generator_component_row w a E c j ha hE r,hc,map_zero]

end Froberg
