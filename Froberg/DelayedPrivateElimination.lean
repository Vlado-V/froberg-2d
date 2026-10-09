module

public import Froberg.CoefficientReconstruction

@[expose] public section

/-! After removing the unique private-private row-two boundary, delayed
pure-output terms vanish inductively. The ordinary even-row elimination then
applies without a further relation hypothesis. -/
noncomputable section
namespace Froberg
open Finset
variable {K A I J : Type*} [Field K] [CommRing A] [Algebra K A]
  [Fintype I] [Fintype J]

/-- A lower-output private term cannot be cancelled by the scalar, new-layer,
and product row. This is the private separation statement used after row two. -/
def PrivateRowSeparation (V W : ℕ → Submodule K A) (a E : I → A)
    (P : J → A) (j : I → ℕ) (r : ℕ) : Prop :=
  ∀ (x b : I → A) (B : I → I → K) (u : J → A),
    (∀ i,x i∈V r) → (∀ i,b i∈V 0) → (∀ k,u k∈W (r-1)) →
    (∀ i k,¬(0<j i ∧ 0<j k ∧ j i+j k=r) → B i k=0) →
    (∑ i,a i*x i)+(∑ i,if j i=r then E i*b i else 0)+
      (∑ i,∑ k,B i k • (E i*E k))+(∑ k,P k*u k)=0 → u=0

/-- Simultaneous induction eliminates every private coefficient and solves
the scalar/even-layer rows; the pure-output term always involves an earlier
private coefficient. -/
theorem solve_rows_with_delayed_private
    (V W : ℕ → Submodule K A) (a E : I → A) (P U : J → A)
    (j : I → ℕ) (c : ℕ → I → A) (u : ℕ → J → A) (d N : ℕ)
    (hd : 2≤d) (hcV : ∀ t i,c t i∈V t) (huW : ∀ t k,u t k∈W t)
    (hE : ∀ i,j i=0 → E i=0) (hu0 : u 0=0) (hu1 : u 1=0)
    (hrow : ∀ r,0<r → r≤N →
      (∑ i,a i*c r i)+(∑ i,if j i≤r then E i*c (r-j i) i else 0)+
      (∑ k,P k*u (r-1) k)+(if d≤r then ∑ k,U k*u (r-d) k else 0)=0)
    (hexact : ∀ r,0<r → r≤N → CoefficientRowExact V a E j r)
    (hseparate : ∀ r,3≤r → r≤N → PrivateRowSeparation V W a E P j r) :
    ∃ B : I → I → K,CoefficientRowsSolved a E j c N B ∧ ∀ t,t<N → u t=0 := by
  classical
  induction N with
  | zero => exact ⟨0,coefficientRowsSolved_zero a E j c,by intros; omega⟩
  | succ N ih =>
    obtain ⟨B,hB,hu⟩ := ih
      (by intro r hr hrN; exact hrow r hr (by omega))
      (by intro r hr hrN; exact hexact r hr (by omega))
      (by intro r hr hrN; exact hseparate r hr (by omega))
    have hUzero : (if d≤N+1 then ∑ k,U k*u (N+1-d) k else 0)=0 := by
      split_ifs with h
      · have ht : N+1-d<N := by omega
        simp only [hu _ ht,Pi.zero_apply,mul_zero,sum_const_zero]
      · rfl
    have hr := hrow (N+1) (by omega) le_rfl
    rw [hUzero,add_zero,show N+1-1=N by omega] at hr
    have huN : u N=0 := by
      by_cases hN0 : N=0
      · simpa only [hN0] using hu0
      by_cases hN1 : N=1
      · simpa only [hN1] using hu1
      have hs := coefficient_row_substitution E j c B (N+1) (by omega) hE
        (by intro t ht htr i; exact hB.representation t ht (by omega) i)
      rw [hs] at hr
      apply hseparate (N+1) (by omega) le_rfl (c (N+1)) (c 0)
        (degreeProductMatrix j (N+1) B) (u N)
        (hcV (N+1)) (hcV 0) (by simpa using huW N)
        (by intro i k h; simp [degreeProductMatrix,h])
      simpa only [add_assoc] using hr
    have hr' : (∑ i,a i*c (N+1) i)+
        (∑ i,if j i≤N+1 then E i*c (N+1-j i) i else 0)=0 := by
      simpa only [huN,Pi.zero_apply,mul_zero,sum_const_zero,add_zero] using hr
    obtain ⟨C,hC⟩ := hB.step V hcV hE hr' (hexact (N+1) (by omega) le_rfl)
    refine ⟨C,hC,?_⟩
    intro t ht
    by_cases heq : t=N
    · simpa only [heq] using huN
    · exact hu t (by omega)

end Froberg
