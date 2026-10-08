import Froberg.OddSplitElimination

/-! Even-parity elimination needs only the even rows constructed in B.4.
The other coefficient rows vanish by parity, without extra rank assumptions. -/
noncomputable section
namespace Froberg
open MvPolynomial
variable {K σ I : Type*} [Field K] [Fintype I] [LinearOrder I]

/-- A genuine even cycle reduces to an embedded scalar cycle using only the
positive even row exactness conditions. -/
theorem polynomial_even_positive_rows_reduce_to_scalar
    (w : σ → ℕ) (hw : ∀ x,w x≤1) (d : ℕ)
    (a E c : I → MvPolynomial σ K) (j : I → ℕ)
    (ha : ∀ i,(a i).IsHomogeneous d ∧ (a i).IsWeightedHomogeneous w 0)
    (hE : ∀ i,(E i).IsWeightedHomogeneous w (j i))
    (hEzero : ∀ i,j i=0 → E i=0) (hj : ∀ i,j i≤d)
    (hjeven : ∀ i,j i%2=0)
    (hc : ∀ i,(c i).IsHomogeneous d)
    (hceven : ∀ i α,(c i).coeff α≠0 → Finsupp.weight w α%2=0)
    (hpositive : ∀ r,0<r → r≤2*d →
      weightedHomogeneousComponent w r (∑ i,(a i+E i)*c i)=0)
    (hexact : ∀ r,0<r → r≤2*d → r%2=0 →
      CoefficientRowExact (coefficientComponentSpace w d) a E j r) :
    ∃ (M : I → I → K) (z : I → MvPolynomial σ K),
      c-matrixBoundary (fun i => a i+E i) M=z ∧
      (∀ i,0<j i → z i=0) ∧
      (∀ i,(z i).IsHomogeneous d ∧ (z i).IsWeightedHomogeneous w 0) := by
  classical
  let V : ℕ → Submodule K (MvPolynomial σ K) :=
    fun t => if t%2=0 then coefficientComponentSpace w d t else ⊥
  have hVzero : V 0=coefficientComponentSpace w d 0 := by simp [V]
  have hrows : ∀ r,0<r → r≤2*d → CoefficientRowExact V a E j r := by
    intro r hr hrd u b B hu hb hB hrel
    by_cases hre : r%2=0
    · apply hexact r hr hrd hre u b B
      · simpa only [V,if_pos hre] using hu
      · simpa only [hVzero] using hb
      · exact hB
      · exact hrel
    · have hu0 (i : I) : u i=0 := by simpa [V,hre] using hu i
      have hne (i : I) : j i≠r := by have := hjeven i; omega
      have hB0 (i k : I) : B i k=0 := by
        apply hB i k
        have hi := hjeven i
        have hk := hjeven k
        omega
      refine ⟨0,?_,?_,?_,?_,?_⟩
      · intros; rfl
      · intro i
        simp [matrixCombination,hu0 i]
      · intro k hk
        exact False.elim (hne k hk)
      · intro i k hi hk hik
        rw [hB0,hB0,neg_zero]
      · intro i hi hii
        exact hB0 i i
  have hmem : ∀ t i,weightedHomogeneousComponent w t (c i)∈V t := by
    intro t i
    by_cases ht : t%2=0
    · rw [show V t=coefficientComponentSpace w d t by simp [V,ht]]
      exact ⟨weightedComponent_preserves_homogeneous w (hc i) t,
        weightedHomogeneousComponent_isWeightedHomogeneous t (c i)⟩
    · rw [weightedComponent_wrong_parity w (c i) 0 t (hceven i) ht]
      exact Submodule.zero_mem _
  obtain ⟨M,z,hz,hzs,hzV⟩ := coefficient_rows_reduce_to_scalar V a E j
    (fun t i => weightedHomogeneousComponent w t (c i)) d c hj hEzero hmem
    (by intro i; rw [hVzero]; exact ha i)
    (fun i => homogeneous_eq_weightedComponents w hw (hc i))
    (fun r hr hrd => by
      rw [← mixed_generator_component_row w a E c j (fun i => (ha i).2) hE r]
      exact hpositive r hr hrd)
    hrows
  exact ⟨M,z,hz,hzs,by intro i; have hi := hzV i; rw [hVzero] at hi; exact hi⟩

end Froberg
