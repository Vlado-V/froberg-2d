module

public import Froberg.DelayedPrivateElimination

@[expose] public section

/-! The solved-row invariant directly reconstructs the literal boundary.
This also applies to the induction with delayed private columns. -/
noncomputable section
namespace Froberg
open Finset
variable {K A I J : Type*} [Field K] [CommRing A] [Algebra K A]
  [Fintype I] [Fintype J]

theorem CoefficientRowsSolved.reduce_to_scalar [LinearOrder I]
    {a E : I → A} {j : I → ℕ} {c : ℕ → I → A} {d : ℕ} {B : I → I → K}
    (hB : CoefficientRowsSolved a E j c (2*d) B)
    (V : ℕ → Submodule K A) (v : I → A)
    (hj : ∀ i,j i≤d) (hE : ∀ i,j i=0 → E i=0)
    (hcV : ∀ t i,c t i∈V t) (haV : ∀ i,a i∈V 0)
    (hv : ∀ i,v i=c 0 i+∑ t∈range d,c (t+1) i) :
    ∃ (M : I → I → K) (z : I → A),
      v-matrixBoundary (fun i => a i+E i) M=z ∧
      (∀ i,0<j i → z i=0) ∧ (∀ i,z i∈V 0) := by
  classical
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


/-- Once the first private boundary has been removed, all remaining private
coefficients vanish and the ordinary coefficients reduce by one literal
constant boundary. Only positive output-row equations are assumed. -/
theorem delayed_private_reduce_to_scalar [LinearOrder I]
    (V W : ℕ → Submodule K A) (a E : I → A) (P U : J → A)
    (j : I → ℕ) (c : ℕ → I → A) (u : ℕ → J → A) (d : ℕ)
    (v : I → A) (w : J → A)
    (hd : 2≤d) (hj : ∀ i,j i≤d)
    (hcV : ∀ t i,c t i∈V t) (huW : ∀ t k,u t k∈W t) (haV : ∀ i,a i∈V 0)
    (hE : ∀ i,j i=0 → E i=0) (hu0 : u 0=0) (hu1 : u 1=0)
    (hv : ∀ i,v i=c 0 i+∑ t∈range d,c (t+1) i)
    (hw : ∀ k,w k=u 0 k+∑ t∈range d,u (t+1) k)
    (hrow : ∀ r,0<r → r≤2*d →
      (∑ i,a i*c r i)+(∑ i,if j i≤r then E i*c (r-j i) i else 0)+
      (∑ k,P k*u (r-1) k)+(if d≤r then ∑ k,U k*u (r-d) k else 0)=0)
    (hexact : ∀ r,0<r → r≤2*d → CoefficientRowExact V a E j r)
    (hseparate : ∀ r,3≤r → r≤2*d → PrivateRowSeparation V W a E P j r) :
    w=0 ∧ ∃ (M : I → I → K) (z : I → A),
      v-matrixBoundary (fun i => a i+E i) M=z ∧
      (∀ i,0<j i → z i=0) ∧ (∀ i,z i∈V 0) := by
  obtain ⟨B,hB,hu⟩ := solve_rows_with_delayed_private V W a E P U j c u d (2*d)
    hd hcV huW hE hu0 hu1 hrow hexact hseparate
  refine ⟨?_,hB.reduce_to_scalar V v hj hE hcV haV hv⟩
  funext k
  rw [hw k,hu0]
  simp only [Pi.zero_apply,zero_add]
  apply Finset.sum_eq_zero
  intro t ht
  have ht' := Finset.mem_range.mp ht
  rw [hu (t+1) (by omega)]
  rfl

end Froberg
