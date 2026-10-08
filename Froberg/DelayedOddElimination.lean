import Froberg.WeightedParitySpace

/-! The odd triangular elimination remains valid after adjoining arbitrary
fixed top-output terms. Its induction only uses lower coefficient rows. -/
noncomputable section
namespace Froberg
open MvPolynomial Finset
variable {K σ I J : Type*} [Field K] [Fintype I] [Fintype J]

/-- Once the first odd coefficient row has been removed, all remaining
coefficients vanish, for every choice of the top forms `U`. -/
theorem delayed_odd_zero
    (w : σ → ℕ) (hw : ∀ x,w x≤1) (d : ℕ) (hd : 3≤d)
    (a E c : I → MvPolynomial σ K) (O U v : J → MvPolynomial σ K)
    (j : I → ℕ)
    (ha : ∀ i,(a i).IsWeightedHomogeneous w 0)
    (hE : ∀ i,(E i).IsWeightedHomogeneous w (j i))
    (hEzero : ∀ i,j i=0 → E i=0)
    (hj : ∀ i,j i%2=0)
    (hO : ∀ k,(O k).IsWeightedHomogeneous w 1)
    (hU : ∀ k,(U k).IsWeightedHomogeneous w d)
    (hc : ∀ i,(c i).IsHomogeneous d) (hv : ∀ k,(v k).IsHomogeneous d)
    (hcodd : ∀ i α,(c i).coeff α≠0 → Finsupp.weight w α%2=1)
    (hveven : ∀ k α,(v k).coeff α≠0 → Finsupp.weight w α%2=0)
    (hcfirst : ∀ i,weightedHomogeneousComponent w 1 (c i)=0)
    (hvfirst : ∀ k,weightedHomogeneousComponent w 0 (v k)=0)
    (hcycle : (∑ i,(a i+E i)*c i)+(∑ k,(O k+U k)*v k)=0)
    (hhigher : ∀ r,3≤r → r≤d+1 → r%2=1 →
      ∀ (x : I → MvPolynomial σ K) (y : J → MvPolynomial σ K),
      (∀ i,x i∈coefficientComponentSpace w d r) →
      (∀ k,y k∈coefficientComponentSpace w d (r-1)) →
      (∑ i,a i*x i)+(∑ k,O k*y k)=0 → x=0 ∧ y=0) : c=0 ∧ v=0 := by
  have hrows : ∀ r,r≤d+1 →
      (∀ i,weightedHomogeneousComponent w r (c i)=0) ∧
      (1≤r → ∀ k,weightedHomogeneousComponent w (r-1) (v k)=0) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro hrd
      by_cases hrp : r%2=1
      · by_cases hr1 : r=1
        · subst r
          exact ⟨hcfirst,fun _ => hvfirst⟩
        have hr : 3≤r := by omega
        have hEc (i : I) : weightedHomogeneousComponent w r (E i*c i)=0 := by
          rw [weightedComponent_homogeneous_left w (hE i)]
          by_cases hji : j i≤r
          · rw [if_pos hji]
            by_cases hj0 : j i=0
            · rw [hEzero i hj0,zero_mul]
            · rw [(ih (r-j i) (by omega) (by omega)).1 i,mul_zero]
          · rw [if_neg hji]
        have hUv (k : J) : weightedHomogeneousComponent w r (U k*v k)=0 := by
          rw [weightedComponent_homogeneous_left w (hU k)]
          by_cases hdr : d≤r
          · rw [if_pos hdr]
            have hz := (ih (r-d+1) (by omega) (by omega)).2 (by omega) k
            rw [Nat.add_sub_cancel] at hz
            rw [hz,mul_zero]
          · rw [if_neg hdr]
        have hrow : (∑ i,a i*weightedHomogeneousComponent w r (c i))+
            (∑ k,O k*weightedHomogeneousComponent w (r-1) (v k))=0 := by
          have h := congrArg (weightedHomogeneousComponent w r) hcycle
          simpa only [map_add,map_sum,map_zero,add_mul,hEc,hUv,
            weightedComponent_homogeneous_left w (ha _),Nat.zero_le,Nat.sub_zero,
            if_true,weightedComponent_homogeneous_left w (hO _),
            if_pos (show 1≤r by omega),add_zero] using h
        obtain ⟨hx,hy⟩ := hhigher r hr hrd hrp
          (fun i => weightedHomogeneousComponent w r (c i))
          (fun k => weightedHomogeneousComponent w (r-1) (v k))
          (fun i => ⟨weightedComponent_preserves_homogeneous w (hc i) r,
            weightedHomogeneousComponent_isWeightedHomogeneous r (c i)⟩)
          (fun k => ⟨weightedComponent_preserves_homogeneous w (hv k) (r-1),
            weightedHomogeneousComponent_isWeightedHomogeneous (r-1) (v k)⟩) hrow
        exact ⟨fun i => congrFun hx i,fun _ k => congrFun hy k⟩
      · refine ⟨fun i => weightedComponent_wrong_parity w (c i) 1 r (hcodd i) hrp,?_⟩
        intro hr k
        exact weightedComponent_wrong_parity w (v k) 0 (r-1) (hveven k) (by omega)
  constructor
  · funext i
    have heq := eq_weightedComponent_of_other_zero w (c i) 0 (by
      intro t ht
      by_cases htd : t≤d+1
      · exact (hrows t htd).1 i
      · exact weightedComponent_above_homogeneous w hw (hc i) (by omega))
    exact heq.trans ((hrows 0 (by omega)).1 i)
  · funext k
    have heq := eq_weightedComponent_of_other_zero w (v k) 0 (by
      intro t ht
      by_cases htd : t≤d
      · simpa only [Nat.add_sub_cancel] using (hrows (t+1) (by omega)).2 (by omega) k
      · exact weightedComponent_above_homogeneous w hw (hv k) (by omega))
    exact heq.trans (hvfirst k)

/-- The full odd background has only literal cross-parity constant Koszul
cycles. In particular, the choice of its pure top-output terms is arbitrary. -/
theorem delayed_odd_cycles
    (w : σ → ℕ) (hw : ∀ x,w x≤1) (d : ℕ) (hd : 3≤d)
    (a E c : I → MvPolynomial σ K) (O U v : J → MvPolynomial σ K)
    (j : I → ℕ)
    (ha : ∀ i,(a i).IsHomogeneous d ∧ (a i).IsWeightedHomogeneous w 0)
    (hE : ∀ i,(E i).IsHomogeneous d ∧ (E i).IsWeightedHomogeneous w (j i))
    (hEzero : ∀ i,j i=0 → E i=0) (hj : ∀ i,j i%2=0)
    (hO : ∀ k,(O k).IsHomogeneous d ∧ (O k).IsWeightedHomogeneous w 1)
    (hU : ∀ k,(U k).IsHomogeneous d ∧ (U k).IsWeightedHomogeneous w d)
    (hUodd : d%2=1 ∨ ∀ k,U k=0)
    (hc : ∀ i,(c i).IsHomogeneous d) (hv : ∀ k,(v k).IsHomogeneous d)
    (hcodd : ∀ i α,(c i).coeff α≠0 → Finsupp.weight w α%2=1)
    (hveven : ∀ k α,(v k).coeff α≠0 → Finsupp.weight w α%2=0)
    (hfirst : ∀ (x : I → MvPolynomial σ K) (y : J → MvPolynomial σ K),
      (∀ i,x i∈coefficientComponentSpace w d 1) →
      (∀ k,y k∈coefficientComponentSpace w d 0) →
      (∑ i,a i*x i)+(∑ k,O k*y k)=0 →
      ∃ B : I → J → K,
        (∀ i,x i=∑ k,B i k • O k) ∧ (∀ k,y k = -∑ i,B i k • a i))
    (hhigher : ∀ r,3≤r → r≤d+1 → r%2=1 →
      ∀ (x : I → MvPolynomial σ K) (y : J → MvPolynomial σ K),
      (∀ i,x i∈coefficientComponentSpace w d r) →
      (∀ k,y k∈coefficientComponentSpace w d (r-1)) →
      (∑ i,a i*x i)+(∑ k,O k*y k)=0 → x=0 ∧ y=0)
    (hcycle : (∑ i,(a i+E i)*c i)+(∑ k,(O k+U k)*v k)=0) :
    ∃ B : I → J → K,
      (∀ i,c i=∑ k,B i k • (O k+U k)) ∧
      (∀ k,v k = -∑ i,B i k • (a i+E i)) := by
  classical
  have hEfirst (i : I) : weightedHomogeneousComponent w 1 (E i*c i)=0 := by
    rw [weightedComponent_homogeneous_left w (hE i).2]
    by_cases hji : j i≤1
    · have hj0 : j i=0 := by have := hj i; omega
      rw [if_pos hji,hEzero i hj0,zero_mul]
    · rw [if_neg hji]
  have hUfirst (k : J) : weightedHomogeneousComponent w 1 (U k*v k)=0 := by
    rw [weightedComponent_homogeneous_left w (hU k).2,if_neg (by omega : ¬d≤1)]
  have hfirstrow : (∑ i,a i*weightedHomogeneousComponent w 1 (c i))+
      (∑ k,O k*weightedHomogeneousComponent w 0 (v k))=0 := by
    have h := congrArg (weightedHomogeneousComponent w 1) hcycle
    simpa only [map_add,map_sum,map_zero,add_mul,hEfirst,hUfirst,
      weightedComponent_homogeneous_left w (ha _).2,Nat.zero_le,Nat.sub_zero,
      if_true,weightedComponent_homogeneous_left w (hO _).2,
      Nat.le_refl,Nat.sub_self,add_zero] using h
  obtain ⟨B,hB,hB'⟩ := hfirst
    (fun i => weightedHomogeneousComponent w 1 (c i))
    (fun k => weightedHomogeneousComponent w 0 (v k))
    (fun i => ⟨weightedComponent_preserves_homogeneous w (hc i) 1,
      weightedHomogeneousComponent_isWeightedHomogeneous 1 (c i)⟩)
    (fun k => ⟨weightedComponent_preserves_homogeneous w (hv k) 0,
      weightedHomogeneousComponent_isWeightedHomogeneous 0 (v k)⟩) hfirstrow
  let c' := fun i => c i-∑ k,B i k • (O k+U k)
  let v' := fun k => v k+∑ i,B i k • (a i+E i)
  have hc' : ∀ i,(c' i).IsHomogeneous d := by
    intro i
    exact (hc i).sub ((homogeneousSubmodule σ K d).sum_mem fun k _ =>
      (homogeneousSubmodule σ K d).smul_mem _ ((hO k).1.add (hU k).1))
  have hv' : ∀ k,(v' k).IsHomogeneous d := by
    intro k
    exact (hv k).add ((homogeneousSubmodule σ K d).sum_mem fun i _ =>
      (homogeneousSubmodule σ K d).smul_mem _ ((ha i).1.add (hE i).1))
  have hUparity (k : J) : U k∈weightedParitySpace w 1 := by
    rcases hUodd with hdodd | hUz
    · exact IsWeightedHomogeneous.mem_parity (hU k).2 hdodd
    · rw [hUz k]
      exact Submodule.zero_mem _
  have hc'odd : ∀ i α,(c' i).coeff α≠0 → Finsupp.weight w α%2=1 := by
    intro i
    apply (mem_weightedParitySpace_iff w 1 (c' i)).mp
    exact (weightedParitySpace w 1).sub_mem
      ((mem_weightedParitySpace_iff w 1 (c i)).mpr (hcodd i))
      ((weightedParitySpace w 1).sum_mem fun k _ =>
        (weightedParitySpace w 1).smul_mem _ ((weightedParitySpace w 1).add_mem
          (IsWeightedHomogeneous.mem_parity (hO k).2 rfl) (hUparity k)))
  have hv'even : ∀ k α,(v' k).coeff α≠0 → Finsupp.weight w α%2=0 := by
    intro k
    apply (mem_weightedParitySpace_iff w 0 (v' k)).mp
    exact (weightedParitySpace w 0).add_mem
      ((mem_weightedParitySpace_iff w 0 (v k)).mpr (hveven k))
      ((weightedParitySpace w 0).sum_mem fun i _ =>
        (weightedParitySpace w 0).smul_mem _ ((weightedParitySpace w 0).add_mem
          (IsWeightedHomogeneous.mem_parity (ha i).2 rfl) (IsWeightedHomogeneous.mem_parity (hE i).2 (hj i))))
  have hc'first (i : I) : weightedHomogeneousComponent w 1 (c' i)=0 := by
    simp only [c',map_sub,map_sum,map_smul,map_add,
      weightedHomogeneousComponent_of_mem (hO _).2,
      weightedHomogeneousComponent_of_mem (hU _).2,ite_true,
      if_neg (by omega : (1:ℕ)≠d),add_zero,hB i,sub_self]
  have hEzeroComp (i : I) : weightedHomogeneousComponent w 0 (E i)=0 := by
    by_cases hi : j i=0
    · rw [hEzero i hi,map_zero]
    · rw [weightedHomogeneousComponent_of_mem (hE i).2,if_neg (Ne.symm hi)]
  have hv'first (k : J) : weightedHomogeneousComponent w 0 (v' k)=0 := by
    simp only [v',map_add,map_sum,map_smul,hEzeroComp,
      weightedHomogeneousComponent_of_mem (ha _).2,ite_true,add_zero,hB' k,neg_add_cancel]
  have hcycle' : (∑ i,(a i+E i)*c' i)+(∑ k,(O k+U k)*v' k)=0 := by
    simp only [c',v',mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib,
      Finset.mul_sum,mul_smul_comm]
    have hs : (∑ i,∑ k,B i k • ((a i+E i)*(O k+U k)))=
        ∑ k,∑ i,B i k • ((O k+U k)*(a i+E i)) := by
      rw [Finset.sum_comm]
      simp only [mul_comm]
    simp only [←mul_add]
    rw [hs]
    linear_combination hcycle
  obtain ⟨hc0,hv0⟩ := delayed_odd_zero w hw d hd a E c' O U v' j
    (fun i => (ha i).2) (fun i => (hE i).2) hEzero hj
    (fun k => (hO k).2) (fun k => (hU k).2) hc' hv' hc'odd hv'even
    hc'first hv'first hcycle' hhigher
  refine ⟨B,?_,?_⟩
  · intro i
    exact sub_eq_zero.mp (congrFun hc0 i)
  · intro k
    exact eq_neg_of_add_eq_zero_left (congrFun hv0 k)

end Froberg
