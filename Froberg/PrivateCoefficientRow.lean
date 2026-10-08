import Froberg.PrivateBiformRow
import Froberg.DelayedPrivateElimination
import Froberg.IntrinsicCoefficientRows
import Froberg.EmptyCoefficientRows

/-! The private-row separation contract for literal core-extended prepared
generators. The sparse family and the private tuple are kept unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Froberg
open Module MvPolynomial PrivateColumns
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {a z b h c m q d R : ℕ}

theorem private_coefficient_row_separation (hd : 3≤d) (hR : 2≤R) (hRd : R+1≤d)
    (bi : Basis (Fin h) K (homogeneousSubmodule σ K R))
    (bo : Basis (Fin c) K (homogeneousSubmodule σ K (R+1)))
    (w : Fin b → homogeneousSubmodule σ K 1) (hw : ∀ i,w i≠0)
    (ι : Fin b ↪ Fin z) (j : Fin q → ℕ)
    (Q : Fin q → Forms K a d) (E : Fin q → MvPolynomial (σ ⊕ Fin a) K)
    (hE : ∀ i,(E i).IsHomogeneous d)
    (hEj : ∀ i,(E i).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 1) (fun _ : Fin a => 0)) (j i))
    (ρ : Fin m ≃ {i : Fin q // j i=R+1})
    (e : Fin m → Fin a →₀ ℕ) (v : Fin m → Fin c → K)
    (hER : ∀ i,E (ρ i).val=polynomialVector (fun k => (bo k).val)
      (fun k => monomial (e i) (v i k)))
    (hprojected : ∀ l t,t≤1 → ∀ p : Fin m → Forms K a t,
      (∀ α,sparseOutputCoefficient e v p α∈(privateOutputMatrix bi bo (w l)).range) → p=0) :
    PrivateRowSeparation
      (coefficientComponentSpace (Sum.elim (fun _ : σ => 1) (fun _ : Fin (a+z) => 0)) d)
      (coefficientComponentSpace (Sum.elim (fun _ : σ => 1) (fun _ : Fin (a+z) => 0)) d)
      (fun i => rename Sum.inr (rename (Fin.castAdd z) (Q i).val))
      (fun i => rename (Sum.map id (Fin.castAdd z)) (E i))
      (fun i => rename Sum.inl (w i).val *
        rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K))) j (R+1) := by
  classical
  intro x f B u hx hf hu hB hrel
  have hxf (i : Fin q) : x i∈biformImage (homogeneousSubmodule σ K (R+1))
      (Forms K (a+z) (d-(R+1))) := by
    apply mem_biformImage_of_homogeneous
    · simpa only [Nat.add_sub_of_le hRd] using (show (x i).IsHomogeneous d from (hx i).1)
    · exact (hx i).2
  have huf (i : Fin b) : u i∈biformImage (homogeneousSubmodule σ K R)
      (Forms K (a+z) (d-R)) := by
    apply mem_biformImage_of_homogeneous
    · simpa only [Nat.add_sub_of_le (by omega : R≤d)] using (show (u i).IsHomogeneous d from (hu i).1)
    · simpa only [Nat.add_sub_cancel] using
      (show (u i).IsWeightedHomogeneous
        (Sum.elim (fun _ : σ => 1) (fun _ : Fin (a+z) => 0)) (R+1-1) from (hu i).2)
  have hf' : ∀ i,∃ ff : Forms K (a+z) d,rename Sum.inr ff.val=f i :=
    fun i => homogeneous_output_zero_exists (hf i).1 (hf i).2
  choose ff hff using hf'
  let p : Fin m → Forms K (a+z) ((d-1)+1) := fun i =>
    ⟨(ff (ρ i).val).val,by simpa only [Nat.sub_add_cancel (by omega : 1≤d)] using (ff (ρ i).val).property⟩
  let C : MvPolynomial (σ ⊕ Fin a) K := ∑ i,∑ k,B i k • (E i*E k)
  have hCd : C.IsHomogeneous (2*d) := by
    change (∑ i,∑ k,B i k • (E i*E k))∈homogeneousSubmodule (σ ⊕ Fin a) K (2*d)
    apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro k _
    exact Submodule.smul_mem _ (B i k) (by
      change (E i*E k).IsHomogeneous (2*d)
      simpa only [two_mul] using (hE i).mul (hE k))
  have hCj : C.IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 1) (fun _ : Fin a => 0)) (R+1) := by
    change (∑ i,∑ k,B i k • (E i*E k))∈weightedHomogeneousSubmodule K
      (Sum.elim (fun _ : σ => 1) (fun _ : Fin a => 0)) (R+1)
    apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro k _
    by_cases hp : 0<j i ∧ 0<j k ∧ j i+j k=R+1
    · exact Submodule.smul_mem _ (B i k) (by
        change (E i*E k).IsWeightedHomogeneous
          (Sum.elim (fun _ : σ => 1) (fun _ : Fin a => 0)) _
        simpa only [hp.2.2] using (hEj i).mul (hEj k))
    · rw [hB i k hp,zero_smul]
      exact Submodule.zero_mem _
  have hCf : C∈biformImage (homogeneousSubmodule σ K (R+1))
      (Forms K a (2*d-(R+1))) := by
    apply mem_biformImage_of_homogeneous
    · simpa only [Nat.add_sub_of_le (by omega : R+1≤2*d)] using hCd
    · exact hCj
  have hnew : (∑ k,polynomialVector (fun l => (bo l).val)
      (fun l => rename (Fin.castAdd z) (monomial (e k) (v k l)))*rename Sum.inr (p k).val)=
      ∑ i,if j i=R+1 then rename (Sum.map id (Fin.castAdd z)) (E i)*f i else 0 := by
    apply Fintype.sum_of_injective (fun k => (ρ k).val)
      (Subtype.val_injective.comp ρ.injective)
    · intro i hi
      have hji : j i≠R+1 := by
        intro hji
        exact hi ⟨ρ.symm ⟨i,hji⟩,by simp⟩
      simp only [if_neg hji]
    · intro k
      rw [if_pos (ρ k).property,hER k,polynomialVector_core_extension]
      change _ * rename Sum.inr (ff (ρ k).val).val=_ * f (ρ k).val
      rw [hff]
  apply private_biform_row_zero (s := d-1) (r := d-R) (t := d-(R+1))
    (by omega) (by omega) (by omega) bi bo w hw ι e v hprojected
    (fun i => (Q i).val) x hxf C hCf p u huf
  rw [hnew]
  simpa only [C,map_sum,map_smul,map_mul] using hrel

/-- The last possible private coefficient lies in pure output degree d.
Its private variable support separates it from every core product. -/
theorem private_coefficient_boundary_row (hd : 3≤d)
    (bi : Basis (Fin h) K (homogeneousSubmodule σ K d))
    (bo : Basis (Fin c) K (homogeneousSubmodule σ K (d+1)))
    (w : Fin b → homogeneousSubmodule σ K 1) (hw : ∀ i,w i≠0)
    (ι : Fin b ↪ Fin z) (j : Fin q → ℕ) (hj : ∀ i,j i≤d)
    (Q : Fin q → Forms K a d) (E : Fin q → MvPolynomial (σ ⊕ Fin a) K)
    (hE : ∀ i,(E i).IsHomogeneous d)
    (hEj : ∀ i,(E i).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 1) (fun _ : Fin a => 0)) (j i)) :
    PrivateRowSeparation
      (coefficientComponentSpace (Sum.elim (fun _ : σ => 1) (fun _ : Fin (a+z) => 0)) d)
      (coefficientComponentSpace (Sum.elim (fun _ : σ => 1) (fun _ : Fin (a+z) => 0)) d)
      (fun i => rename Sum.inr (rename (Fin.castAdd z) (Q i).val))
      (fun i => rename (Sum.map id (Fin.castAdd z)) (E i))
      (fun i => rename Sum.inl (w i).val *
        rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K))) j (d+1) := by
  classical
  intro x f B u hx hf hu hB hrel
  have hx0 (i) : x i=0 := by
    have hi := hx i
    rw [coefficientComponentSpace_above _ (by intro y;cases y <;> simp) (by omega : d<d+1)] at hi
    exact hi
  have hneq (i) : j i≠d+1 := by have := hj i;omega
  let C : MvPolynomial (σ ⊕ Fin a) K := ∑ i,∑ k,B i k • (E i*E k)
  have hCd : C.IsHomogeneous (2*d) := by
    change (∑ i,∑ k,B i k • (E i*E k))∈homogeneousSubmodule (σ ⊕ Fin a) K (2*d)
    apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro k _
    exact Submodule.smul_mem _ (B i k) (by
      change (E i*E k).IsHomogeneous (2*d)
      simpa only [two_mul] using (hE i).mul (hE k))
  have hCj : C.IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 1) (fun _ : Fin a => 0)) (d+1) := by
    change (∑ i,∑ k,B i k • (E i*E k))∈weightedHomogeneousSubmodule K
      (Sum.elim (fun _ : σ => 1) (fun _ : Fin a => 0)) (d+1)
    apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro k _
    by_cases hp : 0<j i ∧ 0<j k ∧ j i+j k=d+1
    · exact Submodule.smul_mem _ (B i k) (by
        change (E i*E k).IsWeightedHomogeneous
          (Sum.elim (fun _ : σ => 1) (fun _ : Fin a => 0)) _
        simpa only [hp.2.2] using (hEj i).mul (hEj k))
    · rw [hB i k hp,zero_smul]
      exact Submodule.zero_mem _
  have hCf : C∈biformImage (homogeneousSubmodule σ K (d+1)) (Forms K a (d-1)) := by
    apply mem_biformImage_of_homogeneous
    · simpa only [show d+1+(d-1)=2*d by omega] using hCd
    · exact hCj
  have huf (i) : u i∈biformImage (homogeneousSubmodule σ K d) (Forms K (a+z) 0) := by
    apply mem_biformImage_of_homogeneous
    · simpa only [Nat.add_zero] using (show (u i).IsHomogeneous d from (hu i).1)
    · simpa only [Nat.add_sub_cancel] using
      (show (u i).IsWeightedHomogeneous
        (Sum.elim (fun _ : σ => 1) (fun _ : Fin (a+z) => 0)) (d+1-1) from (hu i).2)
  apply private_biform_core_zero (s := d-1) (r := 0) (by omega) (by omega)
    bi bo w hw ι C hCf u huf
  simpa only [C,hx0,mul_zero,Finset.sum_const_zero,hneq,ite_false,zero_add,
    map_sum,map_smul,map_mul] using hrel

/-- Above the last private coefficient degree the separation condition is
vacuous, regardless of the other terms in the row. -/
theorem private_coefficient_above_degree (hR : d+1<R)
    (Q E : Fin q → MvPolynomial (σ ⊕ Fin (a+z)) K)
    (P : Fin b → MvPolynomial (σ ⊕ Fin (a+z)) K) (j : Fin q → ℕ) :
    PrivateRowSeparation
      (coefficientComponentSpace (Sum.elim (fun _ : σ => 1) (fun _ : Fin (a+z) => 0)) d)
      (coefficientComponentSpace (Sum.elim (fun _ : σ => 1) (fun _ : Fin (a+z) => 0)) d)
      Q E P j R := by
  intro x f B u hx hf hu hB hrel
  funext i
  have hi := hu i
  rw [coefficientComponentSpace_above _ (by intro y;cases y <;> simp) (by omega : d<R-1)] at hi
  exact hi

end Froberg
