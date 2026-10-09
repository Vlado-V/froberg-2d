module

public import Froberg.BoundedWeightedComponents
public import Froberg.EvenCoefficientElimination

@[expose] public section

/-! Odd-cycle exactness for the scalar-plus-linear polynomial specialization.
Only the degree-one constant kernel and higher-row injectivity are used. -/
noncomputable section
namespace Froberg
open MvPolynomial Finset
variable {K σ I J : Type*} [Field K] [Fintype I] [Fintype J]

/-- If every other weighted component vanishes, extraction is the identity. -/
theorem eq_weightedComponent_of_other_zero (w : σ → ℕ) (f : MvPolynomial σ K) (r : ℕ)
    (hf : ∀ t,t≠r → weightedHomogeneousComponent w t f=0) :
    f=weightedHomogeneousComponent w r f := by
  classical
  ext a
  rw [coeff_weightedHomogeneousComponent]
  by_cases ha : Finsupp.weight w a=r
  · simp [ha]
  · rw [if_neg ha]
    have h := congrArg (fun f : MvPolynomial σ K => f.coeff a) (hf (Finsupp.weight w a) ha)
    simpa [coeff_weightedHomogeneousComponent] using h

/-- A component in the wrong parity is zero. -/
theorem weightedComponent_wrong_parity (w : σ → ℕ) (f : MvPolynomial σ K)
    (p t : ℕ) (hf : ∀ a,f.coeff a≠0 → Finsupp.weight w a%2=p) (ht : t%2≠p) :
    weightedHomogeneousComponent w t f=0 := by
  apply weightedHomogeneousComponent_eq_zero'
  intro a ha heq
  exact ht (heq ▸ hf a (mem_support_iff.mp ha))

/-- Every odd cycle of a scalar list S and a linear-output list O is a
literal constant S–O Koszul vector. -/
theorem scalar_linear_odd_cycles
    (w : σ → ℕ) (hw : ∀ x,w x≤1) (d : ℕ)
    (S : I → MvPolynomial σ K) (O : J → MvPolynomial σ K)
    (hS : ∀ i,(S i).IsWeightedHomogeneous w 0)
    (hO : ∀ j,(O j).IsWeightedHomogeneous w 1)
    (hfirst : ∀ (u : I → MvPolynomial σ K) (v : J → MvPolynomial σ K),
      (∀ i,u i∈coefficientComponentSpace w d 1) →
      (∀ j,v j∈coefficientComponentSpace w d 0) →
      (∑ i,S i*u i)+(∑ j,O j*v j)=0 →
      ∃ B : I → J → K,
        (∀ i,u i=∑ j,B i j • O j) ∧ (∀ j,v j = -∑ i,B i j • S i))
    (hhigher : ∀ r,3≤r → r≤d+1 → r%2=1 →
      ∀ (u : I → MvPolynomial σ K) (v : J → MvPolynomial σ K),
      (∀ i,u i∈coefficientComponentSpace w d r) →
      (∀ j,v j∈coefficientComponentSpace w d (r-1)) →
      (∑ i,S i*u i)+(∑ j,O j*v j)=0 → u=0 ∧ v=0)
    (c : I → MvPolynomial σ K) (e : J → MvPolynomial σ K)
    (hc : ∀ i,(c i).IsHomogeneous d) (he : ∀ j,(e j).IsHomogeneous d)
    (hcodd : ∀ i a,(c i).coeff a≠0 → Finsupp.weight w a%2=1)
    (heeven : ∀ j a,(e j).coeff a≠0 → Finsupp.weight w a%2=0)
    (hcycle : (∑ i,S i*c i)+(∑ j,O j*e j)=0) :
    ∃ B : I → J → K,
      (∀ i,c i=∑ j,B i j • O j) ∧ (∀ j,e j = -∑ i,B i j • S i) := by
  have hmemS (r : ℕ) (i : I) :
      weightedHomogeneousComponent w r (c i)∈coefficientComponentSpace w d r :=
    ⟨weightedComponent_preserves_homogeneous w (hc i) r,
      weightedHomogeneousComponent_isWeightedHomogeneous r (c i)⟩
  have hmemO (r : ℕ) (j : J) :
      weightedHomogeneousComponent w r (e j)∈coefficientComponentSpace w d r :=
    ⟨weightedComponent_preserves_homogeneous w (he j) r,
      weightedHomogeneousComponent_isWeightedHomogeneous r (e j)⟩
  have hrow (r : ℕ) (hr : 0<r) :
      (∑ i,S i*weightedHomogeneousComponent w r (c i))+
      (∑ j,O j*weightedHomogeneousComponent w (r-1) (e j))=0 := by
    have h := congrArg (weightedHomogeneousComponent w r) hcycle
    simpa only [map_add,map_sum,map_zero,weightedComponent_homogeneous_left w (hS _),
      Nat.zero_le,Nat.sub_zero,if_true,weightedComponent_homogeneous_left w (hO _),
      if_pos (show 1≤r by omega)] using h
  have hhigh (r : ℕ) (hr : 3≤r) (hrd : r≤d+1) (hrp : r%2=1) :=
    hhigher r hr hrd hrp (fun i => weightedHomogeneousComponent w r (c i))
      (fun j => weightedHomogeneousComponent w (r-1) (e j)) (hmemS r) (hmemO (r-1))
      (hrow r (by omega))
  have hccomp (i : I) : c i=weightedHomogeneousComponent w 1 (c i) := by
    apply eq_weightedComponent_of_other_zero
    intro t ht
    by_cases htd : d<t
    · exact weightedComponent_above_homogeneous w hw (hc i) htd
    by_cases htp : t%2=1
    · have h := (hhigh t (by omega) (by omega) htp).1
      exact congrFun h i
    · exact weightedComponent_wrong_parity w (c i) 1 t (hcodd i) htp
  have hecomp (j : J) : e j=weightedHomogeneousComponent w 0 (e j) := by
    apply eq_weightedComponent_of_other_zero
    intro t ht
    by_cases htd : d<t
    · exact weightedComponent_above_homogeneous w hw (he j) htd
    by_cases htp : t%2=0
    · have h := (hhigh (t+1) (by omega) (by omega) (by omega)).2
      simpa only [Nat.add_sub_cancel,Pi.zero_apply] using congrFun h j
    · exact weightedComponent_wrong_parity w (e j) 0 t (heeven j) htp
  obtain ⟨B,hB,hB'⟩ := hfirst
    (fun i => weightedHomogeneousComponent w 1 (c i))
    (fun j => weightedHomogeneousComponent w 0 (e j))
    (hmemS 1) (hmemO 0) (by simpa using hrow 1 (by omega))
  exact ⟨B,fun i => (hccomp i).trans (hB i),fun j => (hecomp j).trans (hB' j)⟩

end Froberg
