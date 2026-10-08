import Froberg.PrivatePolynomialElimination
import Froberg.PrivateBoundaryRemoval
import Froberg.WeightedParitySpace

/-! Removing the actual private-private boundary and performing delayed
elimination yields the complete even coefficient reduction for U+P. -/
noncomputable section
namespace Froberg
open MvPolynomial
variable {K σ I : Type*} [Field K] [Fintype I] [LinearOrder I] {b : ℕ}

theorem matrixBoundary_mem_submodule (V : Submodule K (MvPolynomial σ K))
    (q : Fin b → MvPolynomial σ K) (hq : ∀ i,q i∈V)
    (C : Fin b → Fin b → K) (i : Fin b) : matrixBoundary q C i∈V := by
  apply V.sub_mem
  · exact V.sum_mem (fun k _ => V.smul_mem _ (hq k))
  · exact V.sum_mem (fun k _ => V.smul_mem _ (hq k))

theorem private_complete_positive_reduction
    (w : σ → ℕ) (hw : ∀ x,w x≤1) (d : ℕ) (hd : 3≤d) (hodd : d%2=1)
    (a E c : I → MvPolynomial σ K) (P U v : Fin b → MvPolynomial σ K) (j : I → ℕ)
    (ha : ∀ i,(a i).IsHomogeneous d ∧ (a i).IsWeightedHomogeneous w 0)
    (hE : ∀ i,(E i).IsWeightedHomogeneous w (j i))
    (hP : ∀ k,(P k).IsHomogeneous d ∧ (P k).IsWeightedHomogeneous w 1)
    (hU : ∀ k,(U k).IsHomogeneous d ∧ (U k).IsWeightedHomogeneous w d)
    (hEzero : ∀ i,j i=0 → E i=0) (hj : ∀ i,j i≤d) (hjeven : ∀ i,j i%2=0)
    (hc : ∀ i,(c i).IsHomogeneous d) (hv : ∀ k,(v k).IsHomogeneous d)
    (hceven : ∀ i α,(c i).coeff α≠0 → Finsupp.weight w α%2=0)
    (hvodd : ∀ k α,(v k).coeff α≠0 → Finsupp.weight w α%2=1)
    (hfirst : (fun k => weightedHomogeneousComponent w 1 (v k))∈
      Submodule.span K (Set.range (koszulVector P)))
    (hpositive : ∀ r,0<r → r≤2*d → weightedHomogeneousComponent w r
      ((∑ i,(a i+E i)*c i)+(∑ k,(P k+U k)*v k))=0)
    (hexact : ∀ r,0<r → r≤2*d → r%2=0 →
      CoefficientRowExact (coefficientComponentSpace w d) a E j r)
    (hseparate : ∀ r,3≤r → r≤2*d → r%2=0 →
      PrivateRowSeparation (coefficientComponentSpace w d) (coefficientComponentSpace w d) a E P j r) :
    ∃ (C : Fin b → Fin b → K) (M : I → I → K) (z : I → MvPolynomial σ K),
      v=matrixBoundary (fun k => P k+U k) C ∧
      c-matrixBoundary (fun i => a i+E i) M=z ∧
      (∀ i,0<j i → z i=0) ∧
      (∀ i,(z i).IsHomogeneous d ∧ (z i).IsWeightedHomogeneous w 0) := by
  obtain ⟨C,hfirst',hsum⟩ := remove_private_first_component w U P v (by omega)
    (fun k => (hU k).2) (fun k => (hP k).2) hfirst
  let v' := v-matrixBoundary (fun k => U k+P k) C
  have hv' : ∀ k,(v' k).IsHomogeneous d := by
    intro k
    exact (hv k).sub (matrixBoundary_mem_submodule (homogeneousSubmodule σ K d) _
      (fun k => (hU k).1.add (hP k).1) C k)
  have hp' : ∀ k α,(v' k).coeff α≠0 → Finsupp.weight w α%2=1 := by
    intro k
    apply (mem_weightedParitySpace_iff w 1 (v' k)).mp
    exact (weightedParitySpace w 1).sub_mem
      ((mem_weightedParitySpace_iff w 1 (v k)).mpr (hvodd k))
      (matrixBoundary_mem_submodule (weightedParitySpace w 1) _
        (fun k => (weightedParitySpace w 1).add_mem
          (IsWeightedHomogeneous.mem_parity (hU k).2 hodd)
          (IsWeightedHomogeneous.mem_parity (hP k).2 rfl)) C k)
  obtain ⟨hvzero,M,z,hz,hzs,hzV⟩ := private_polynomial_positive_rows_reduce w hw d (by omega)
    a E c P U v' j ha hE (fun k => (hP k).2) (fun k => (hU k).2)
    hEzero hj hjeven hc hv' hceven hp' hfirst' (by
      intro r hr hrd
      have hs : (∑ k,(P k+U k)*v' k)=(∑ k,(P k+U k)*v k) := by
        simpa only [v',add_comm] using hsum
      rw [hs]
      exact hpositive r hr hrd) hexact hseparate
  refine ⟨C,M,z,?_,hz,hzs,hzV⟩
  funext k
  have hk := congrFun hvzero k
  change v k-matrixBoundary (fun k => U k+P k) C k=0 at hk
  simpa only [add_comm] using (sub_eq_zero.mp hk)

end Froberg
