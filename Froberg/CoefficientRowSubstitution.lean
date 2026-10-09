module

public import Froberg.MixedRowComponents
public import Froberg.GradedKoszulElimination

@[expose] public section

/-! Exact substitution of previously solved coefficient rows. The remaining
nonlinear-looking terms are constants times products of two positive layers. -/
noncomputable section
namespace Froberg
open Finset
variable {K A I : Type*} [Field K] [CommRing A] [Algebra K A] [Fintype I]

/-- The constant matrix contributing to one total output degree. -/
def degreeProductMatrix (j : I → ℕ) (r : ℕ) (B : I → I → K) (i k : I) : K :=
  if 0<j i ∧ 0<j k ∧ j i+j k=r then B i k else 0

/-- At row r, every already represented positive coefficient gives a literal
product of two generator layers. The degree-zero coefficient is kept separate. -/
theorem coefficient_row_substitution
    (E : I → A) (j : I → ℕ) (c : ℕ → I → A) (B : I → I → K)
    (r : ℕ) (hr : 0<r)
    (hE : ∀ i,j i=0 → E i=0)
    (hc : ∀ t,0<t → t<r → ∀ i,
      c t i=∑ k,if j k=t then B i k • E k else 0) :
    (∑ i,if j i≤r then E i*c (r-j i) i else 0) =
      (∑ i,if j i=r then E i*c 0 i else 0) +
      ∑ i,∑ k,degreeProductMatrix j r B i k • (E i*E k) := by
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  by_cases hzero : j i=0
  · simp [hzero,hE i hzero,degreeProductMatrix]
  by_cases heq : j i=r
  · have hmat : ∀ k,degreeProductMatrix j r B i k=0 := by
      intro k
      unfold degreeProductMatrix
      split_ifs with h
      · omega
      · rfl
    simp [heq,hmat]
  by_cases hlt : j i<r
  · have ht : 0<r-j i := by omega
    have htr : r-j i<r := by omega
    rw [if_pos (Nat.le_of_lt hlt),if_neg heq,zero_add,hc _ ht htr i,mul_sum]
    apply sum_congr rfl
    intro k hk
    by_cases hkdeg : j k=r-j i
    · have hkpos : 0<j k := by omega
      have hsum : j i+j k=r := by omega
      rw [if_pos hkdeg,degreeProductMatrix,if_pos ⟨by omega,hkpos,hsum⟩]
      exact mul_smul_comm _ _ _
    · have hmat : ¬(0<j i ∧ 0<j k ∧ j i+j k=r) := by omega
      simp [hkdeg,degreeProductMatrix,hmat]
  · have hgt : r<j i := by omega
    have hmat : ∀ k,degreeProductMatrix j r B i k=0 := by
      intro k
      unfold degreeProductMatrix
      split_ifs with h
      · omega
      · rfl
    simp [show ¬j i≤r by omega,heq,hmat]

/-- The actual polynomial cycle equation becomes the linear scalar/new-layer
row plus the formal product row after substituting earlier components. -/
theorem mixed_cycle_substituted_row {σ : Type*}
    (w : σ → ℕ) (a E c : I → MvPolynomial σ K) (j : I → ℕ)
    (ha : ∀ i,(a i).IsWeightedHomogeneous w 0)
    (hE : ∀ i,(E i).IsWeightedHomogeneous w (j i))
    (hEzero : ∀ i,j i=0 → E i=0)
    (hcycle : ∑ i,(a i+E i)*c i=0)
    (B : I → I → K) (r : ℕ) (hr : 0<r)
    (hc : ∀ t,0<t → t<r → ∀ i,
      MvPolynomial.weightedHomogeneousComponent w t (c i)=
        ∑ k,if j k=t then B i k • E k else 0) :
    (∑ i,a i*MvPolynomial.weightedHomogeneousComponent w r (c i)) +
      (∑ i,if j i=r then E i*MvPolynomial.weightedHomogeneousComponent w 0 (c i) else 0) +
      (∑ i,∑ k,degreeProductMatrix j r B i k • (E i*E k))=0 := by
  have h := mixed_cycle_row w a E c j ha hE hcycle r
  rw [coefficient_row_substitution E j
    (fun t i => MvPolynomial.weightedHomogeneousComponent w t (c i)) B r hr hEzero hc] at h
  simpa only [add_assoc] using h

end Froberg
