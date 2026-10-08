import Froberg.CoefficientRowElimination
import Froberg.ScalarCycleReduction

/-! Reconstruct actual coefficients from the solved rows and remove their
positive part by one constant Koszul boundary. -/
noncomputable section
namespace Froberg
open Finset
variable {K A I : Type*} [Field K] [CommRing A] [Algebra K A] [Fintype I]

/-- Once all coefficient degrees have been processed, the matrix reconstructs
the complete positive part of every coefficient. -/
theorem CoefficientRowsSolved.reconstruct
    {a E : I → A} {j : I → ℕ} {c : ℕ → I → A} {d : ℕ} {B : I → I → K}
    (hB : CoefficientRowsSolved a E j c (2*d) B)
    (hj : ∀ i,j i≤d) (v : I → A)
    (hv : ∀ i,v i=c 0 i+∑ t∈range d,c (t+1) i) :
    ∀ i,v i=c 0 i+matrixCombination E B i := by
  classical
  intro i
  rw [hv i]
  congr 1
  have hs : ∑ t∈range d,c (t+1) i =
      ∑ t∈range d,∑ k,if j k=t+1 then B i k • E k else 0 := by
    apply sum_congr rfl
    intro t ht
    exact hB.representation (t+1) (by omega) (by have := mem_range.mp ht; omega) i
  rw [hs,sum_comm]
  unfold matrixCombination
  apply sum_congr rfl
  intro k hk
  by_cases hk0 : j k=0
  · simp [hk0,hB.support i k (Or.inl hk0)]
  · have hkpos : 0<j k := by omega
    have hkm : j k-1∈range d := mem_range.mpr (by have := hj k; omega)
    rw [sum_eq_single (j k-1)]
    · rw [if_pos (by omega)]
    · intro t ht hne
      rw [if_neg (by omega)]
    · exact fun h => False.elim (h hkm)

/-- Vanishing positive coefficient rows reduce to scalar-supported coefficients
by an explicit constant Koszul boundary, without a degree-zero equation. -/
theorem coefficient_rows_reduce_to_scalar [LinearOrder I]
    (V : ℕ → Submodule K A) (a E : I → A) (j : I → ℕ)
    (c : ℕ → I → A) (d : ℕ) (v : I → A)
    (hj : ∀ i,j i≤d) (hE : ∀ i,j i=0 → E i=0)
    (hcV : ∀ t i,c t i∈V t) (haV : ∀ i,a i∈V 0)
    (hv : ∀ i,v i=c 0 i+∑ t∈range d,c (t+1) i)
    (hrow : ∀ r,0<r → r≤2*d → (∑ i,a i*c r i)+
      (∑ i,if j i≤r then E i*c (r-j i) i else 0)=0)
    (hexact : ∀ r,0<r → r≤2*d → CoefficientRowExact V a E j r) :
    ∃ (M : I → I → K) (z : I → A),
      v-matrixBoundary (fun i => a i+E i) M=z ∧
      (∀ i,0<j i → z i=0) ∧
      (∀ i,z i∈V 0) := by
  classical
  obtain ⟨B,hB⟩ := exists_solved_coefficient_matrix V a E j c (2*d) hcV hE hrow hexact
  let P := univ.filter (fun i => 0<j i)
  have hP (i : I) : i∈P ↔ 0<j i := by simp [P]
  have hE' : ∀ i∉P,E i=0 := by
    intro i hi
    have hn : ¬0<j i := fun h => hi ((hP i).mpr h)
    exact hE i (by omega)
  have hzero : ∀ i k,k∉P → B i k=0 := by
    intro i k hk
    have hn : ¬0<j k := fun h => hk ((hP k).mpr h)
    exact hB.support i k (Or.inl (by omega))
  have hskew : ∀ i∈P,∀ k∈P,B i k = -B k i := by
    intro i hi k hk
    exact hB.skew i k ((hP i).mp hi) ((hP k).mp hk) (by have := hj i; have := hj k; omega)
  have hdiag : ∀ i∈P,B i i=0 := by
    intro i hi
    exact hB.diagonal i ((hP i).mp hi) (by have := hj i; omega)
  have hb : ∀ k∈P,c 0 k = -∑ i,B i k • a i := by
    intro k hk
    exact hB.scalar k ((hP k).mp hk) (by have := hj k; omega)
  let M := lowerMatrix (alternatingCompletion P B)
  let z := fun i => if i∈P then 0 else c 0 i-∑ k∈P,B i k • a k
  have hrepr : v=(fun i => c 0 i+matrixCombination E B i) := funext (hB.reconstruct hj v hv)
  have hz : v-matrixBoundary (fun i => a i+E i) M=z := by
    rw [hrepr]
    exact scalar_cycle_reduction P a E (c 0) B hE' hzero hskew hdiag hb
  refine ⟨M,z,hz,?_,?_⟩
  · intro i hi
    simp [z,(hP i).mpr hi]
  · intro i
    by_cases hi : i∈P
    · simp only [z,if_pos hi]
      exact (V 0).zero_mem
    · simp only [z,if_neg hi]
      apply (V 0).sub_mem (hcV 0 i)
      apply Submodule.sum_mem
      intro k hk
      exact (V 0).smul_mem (B i k) (haV k)

/-- If the original relation also vanishes in degree zero, the scalar
remainder is an actual scalar cycle. -/
theorem coefficient_rows_reduce_to_scalar_cycle [LinearOrder I]
    (V : ℕ → Submodule K A) (a E : I → A) (j : I → ℕ)
    (c : ℕ → I → A) (d : ℕ) (v : I → A)
    (hj : ∀ i,j i≤d) (hE : ∀ i,j i=0 → E i=0)
    (hcV : ∀ t i,c t i∈V t) (haV : ∀ i,a i∈V 0)
    (hv : ∀ i,v i=c 0 i+∑ t∈range d,c (t+1) i)
    (hrow : ∀ r,0<r → r≤2*d → (∑ i,a i*c r i)+
      (∑ i,if j i≤r then E i*c (r-j i) i else 0)=0)
    (hexact : ∀ r,0<r → r≤2*d → CoefficientRowExact V a E j r)
    (hcycle : ∑ i,(a i+E i)*v i=0) :
    ∃ (M : I → I → K) (z : I → A),
      v-matrixBoundary (fun i => a i+E i) M=z ∧
      (∀ i,0<j i → z i=0) ∧ (∀ i,z i∈V 0) ∧ ∑ i,a i*z i=0 := by
  obtain ⟨M,z,hz,hzs,hzV⟩ := coefficient_rows_reduce_to_scalar V a E j c d v
    hj hE hcV haV hv hrow hexact
  refine ⟨M,z,hz,hzs,hzV,?_⟩
  have hzeroCycle : ∑ i,(a i+E i)*z i=0 := by
    rw [← hz]
    simp only [Pi.sub_apply,mul_sub,sum_sub_distrib,hcycle,matrixBoundary_cycle,sub_self]
  convert hzeroCycle using 1
  apply sum_congr rfl
  intro i hi
  by_cases hji : 0<j i
  · rw [hzs i hji,mul_zero,mul_zero]
  · rw [hE i (by omega),add_zero]

end Froberg
