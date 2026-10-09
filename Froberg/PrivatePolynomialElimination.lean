module

public import Froberg.SolvedCoefficientReduction
public import Froberg.EvenParityElimination

@[expose] public section

/-! Literal polynomial reconstruction for the odd-degree prepared background,
after the first private-private boundary has been removed. -/
noncomputable section
namespace Froberg
open MvPolynomial Finset
variable {K σ I J : Type*} [Field K] [Fintype I] [LinearOrder I] [Fintype J]

theorem private_polynomial_positive_rows_reduce
    (w : σ → ℕ) (hw : ∀ x,w x≤1) (d : ℕ) (hd : 2≤d)
    (a E c : I → MvPolynomial σ K) (P U v : J → MvPolynomial σ K) (j : I → ℕ)
    (ha : ∀ i,(a i).IsHomogeneous d ∧ (a i).IsWeightedHomogeneous w 0)
    (hE : ∀ i,(E i).IsWeightedHomogeneous w (j i))
    (hP : ∀ k,(P k).IsWeightedHomogeneous w 1)
    (hU : ∀ k,(U k).IsWeightedHomogeneous w d)
    (hEzero : ∀ i,j i=0 → E i=0) (hj : ∀ i,j i≤d) (hjeven : ∀ i,j i%2=0)
    (hc : ∀ i,(c i).IsHomogeneous d) (hv : ∀ k,(v k).IsHomogeneous d)
    (hceven : ∀ i α,(c i).coeff α≠0 → Finsupp.weight w α%2=0)
    (hvodd : ∀ k α,(v k).coeff α≠0 → Finsupp.weight w α%2=1)
    (hfirst : ∀ k,weightedHomogeneousComponent w 1 (v k)=0)
    (hpositive : ∀ r,0<r → r≤2*d → weightedHomogeneousComponent w r
      ((∑ i,(a i+E i)*c i)+(∑ k,(P k+U k)*v k))=0)
    (hexact : ∀ r,0<r → r≤2*d → r%2=0 →
      CoefficientRowExact (coefficientComponentSpace w d) a E j r)
    (hseparate : ∀ r,3≤r → r≤2*d → r%2=0 →
      PrivateRowSeparation (coefficientComponentSpace w d) (coefficientComponentSpace w d) a E P j r) :
    v=0 ∧ ∃ (M : I → I → K) (z : I → MvPolynomial σ K),
      c-matrixBoundary (fun i => a i+E i) M=z ∧
      (∀ i,0<j i → z i=0) ∧
      (∀ i,(z i).IsHomogeneous d ∧ (z i).IsWeightedHomogeneous w 0) := by
  classical
  let V : ℕ → Submodule K (MvPolynomial σ K) :=
    fun t => if t%2=0 then coefficientComponentSpace w d t else ⊥
  let W : ℕ → Submodule K (MvPolynomial σ K) :=
    fun t => if t%2=1 then coefficientComponentSpace w d t else ⊥
  have hVzero : V 0=coefficientComponentSpace w d 0 := by simp [V]
  have hrows : ∀ r,0<r → r≤2*d → CoefficientRowExact V a E j r := by
    intro r hr hrd x b B hx hb hB hrel
    by_cases hre : r%2=0
    · apply hexact r hr hrd hre x b B
      · simpa only [V,if_pos hre] using hx
      · simpa only [hVzero] using hb
      · exact hB
      · exact hrel
    · have hx0 (i : I) : x i=0 := by simpa [V,hre] using hx i
      have hne (i : I) : j i≠r := by have := hjeven i; omega
      have hB0 (i k : I) : B i k=0 := by
        apply hB i k
        have hi := hjeven i
        have hk := hjeven k
        omega
      refine ⟨0,?_,?_,?_,?_,?_⟩
      · intros; rfl
      · intro i; simp [matrixCombination,hx0 i]
      · intro k hk; exact False.elim (hne k hk)
      · intro i k hi hk hik; rw [hB0,hB0,neg_zero]
      · intro i hi hii; exact hB0 i i
  have hsep : ∀ r,3≤r → r≤2*d → PrivateRowSeparation V W a E P j r := by
    intro r hr hrd x b B u hx hb hu hB hrel
    by_cases hre : r%2=0
    · apply hseparate r hr hrd hre x b B u
      · simpa only [V,if_pos hre] using hx
      · simpa only [hVzero] using hb
      · have hodd : (r-1)%2=1 := by omega
        simpa only [W,if_pos hodd] using hu
      · exact hB
      · exact hrel
    · have hnodd : (r-1)%2≠1 := by omega
      funext k
      have hk := hu k
      simpa [W,hnodd] using hk
  have hcV : ∀ t i,weightedHomogeneousComponent w t (c i)∈V t := by
    intro t i
    by_cases ht : t%2=0
    · rw [show V t=coefficientComponentSpace w d t by simp [V,ht]]
      exact ⟨weightedComponent_preserves_homogeneous w (hc i) t,
        weightedHomogeneousComponent_isWeightedHomogeneous t (c i)⟩
    · rw [weightedComponent_wrong_parity w (c i) 0 t (hceven i) ht]
      exact Submodule.zero_mem _
  have hvW : ∀ t k,weightedHomogeneousComponent w t (v k)∈W t := by
    intro t k
    by_cases ht : t%2=1
    · rw [show W t=coefficientComponentSpace w d t by simp [W,ht]]
      exact ⟨weightedComponent_preserves_homogeneous w (hv k) t,
        weightedHomogeneousComponent_isWeightedHomogeneous t (v k)⟩
    · rw [weightedComponent_wrong_parity w (v k) 1 t (hvodd k) ht]
      exact Submodule.zero_mem _
  obtain ⟨hvzero,M,z,hz,hzs,hzV⟩ := delayed_private_reduce_to_scalar V W a E P U j
    (fun t i => weightedHomogeneousComponent w t (c i))
    (fun t k => weightedHomogeneousComponent w t (v k)) d c v hd hj hcV hvW
    (by intro i; rw [hVzero]; exact ha i) hEzero
    (by funext k; exact weightedComponent_wrong_parity w (v k) 1 0 (hvodd k) (by decide))
    (funext hfirst)
    (fun i => homogeneous_eq_weightedComponents w hw (hc i))
    (fun k => homogeneous_eq_weightedComponents w hw (hv k))
    (by
      intro r hr hrd
      have hh := hpositive r hr hrd
      rw [map_add,mixed_generator_component_row w a E c j (fun i => (ha i).2) hE r] at hh
      simp only [map_sum,add_mul,map_add,Finset.sum_add_distrib,
        weightedComponent_homogeneous_left w (hP _),
        weightedComponent_homogeneous_left w (hU _),if_pos (by omega : 1≤r)] at hh
      by_cases hrd' : d≤r
      · simpa only [if_pos hrd',add_assoc] using hh
      · simpa only [if_neg hrd',Finset.sum_const_zero,add_zero,add_assoc] using hh)
    hrows hsep
  refine ⟨hvzero,M,z,hz,hzs,?_⟩
  intro i
  have hi := hzV i
  rw [hVzero] at hi
  exact hi

end Froberg
