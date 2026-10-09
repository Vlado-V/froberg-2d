module

public import Froberg.CoefficientRowSubstitution

@[expose] public section

/-! Increasing-degree elimination from exact scalar/new-layer/product rows.
The induction retains a coefficient matrix and performs no division. -/
noncomputable section
namespace Froberg
open Finset
variable {K A I : Type*} [Field K] [CommRing A] [Algebra K A] [Fintype I]

/-- Exactness of a single coefficient row, with its scalar, new-layer, and
formal product summands stated separately. -/
def CoefficientRowExact (V : ℕ → Submodule K A) (a E : I → A) (j : I → ℕ) (r : ℕ) : Prop :=
  ∀ (u b : I → A) (B : I → I → K),
    (∀ i,u i∈V r) → (∀ i,b i∈V 0) →
    (∀ i k,¬(0<j i ∧ 0<j k ∧ j i+j k=r) → B i k=0) →
    (∑ i,a i*u i)+(∑ i,if j i=r then E i*b i else 0)+
      (∑ i,∑ k,B i k • (E i*E k))=0 →
    ∃ C : I → I → K,
      (∀ i k,j k≠r → C i k=0) ∧
      (∀ i,u i=matrixCombination E C i) ∧
      (∀ k,j k=r → b k = -∑ i,C i k • a i) ∧
      (∀ i k,0<j i → 0<j k → j i+j k=r → B i k = -B k i) ∧
      (∀ i,0<j i → j i+j i=r → B i i=0)

/-- The invariant after all rows through N have been solved. -/
structure CoefficientRowsSolved (a E : I → A) (j : I → ℕ)
    (c : ℕ → I → A) (N : ℕ) (B : I → I → K) : Prop where
  support : ∀ i k,j k=0 ∨ N<j k → B i k=0
  representation : ∀ t,0<t → t≤N → ∀ i,
    c t i=∑ k,if j k=t then B i k • E k else 0
  scalar : ∀ k,0<j k → j k≤N → c 0 k = -∑ i,B i k • a i
  skew : ∀ i k,0<j i → 0<j k → j i+j k≤N → B i k = -B k i
  diagonal : ∀ i,0<j i → j i+j i≤N → B i i=0

/-- The zero matrix is the initial state before the first positive row. -/
theorem coefficientRowsSolved_zero (a E : I → A) (j : I → ℕ) (c : ℕ → I → A) :
    CoefficientRowsSolved a E j c 0 (0 : I → I → K) := by
  constructor
  · intros; rfl
  · intros; omega
  · intros; omega
  · intros; omega
  · intros; omega

/-- One exact row extends the solved matrix by its new columns, preserving
every earlier coefficient and every earlier alternating relation. -/
theorem CoefficientRowsSolved.step
    {a E : I → A} {j : I → ℕ} {c : ℕ → I → A} {N : ℕ} {B : I → I → K}
    (hB : CoefficientRowsSolved a E j c N B)
    (V : ℕ → Submodule K A) (hcV : ∀ t i,c t i∈V t)
    (hE : ∀ i,j i=0 → E i=0)
    (hrow : (∑ i,a i*c (N+1) i)+
      (∑ i,if j i≤N+1 then E i*c (N+1-j i) i else 0)=0)
    (hexact : CoefficientRowExact V a E j (N+1)) :
    ∃ C : I → I → K,CoefficientRowsSolved a E j c (N+1) C := by
  classical
  have hsub := coefficient_row_substitution E j c B (N+1) (by omega) hE (by
    intro t ht htr i
    exact hB.representation t ht (by omega) i)
  rw [hsub] at hrow
  have hrow' : (∑ i,a i*c (N+1) i)+(∑ i,if j i=N+1 then E i*c 0 i else 0)+
      (∑ i,∑ k,degreeProductMatrix j (N+1) B i k • (E i*E k))=0 := by
    simpa only [add_assoc] using hrow
  obtain ⟨D,hDs,hDr,hDb,hDsk,hDd⟩ := hexact (c (N+1)) (c 0)
    (degreeProductMatrix j (N+1) B) (hcV (N+1)) (hcV 0)
    (by intro i k h; simp [degreeProductMatrix,h]) hrow'
  refine ⟨fun i k => B i k+D i k,?_⟩
  constructor
  · intro i k hk
    have hBk : j k=0 ∨ N<j k := by omega
    have hDk : j k≠N+1 := by omega
    rw [hB.support i k hBk,hDs i k hDk,add_zero]
  · intro t ht htN i
    by_cases hteq : t=N+1
    · subst t
      rw [hDr i]
      unfold matrixCombination
      apply sum_congr rfl
      intro k hk
      by_cases hkt : j k=N+1
      · rw [if_pos hkt,hB.support i k (Or.inr (by omega)),zero_add]
      · rw [if_neg hkt,hDs i k hkt,zero_smul]
    · rw [hB.representation t ht (by omega) i]
      apply sum_congr rfl
      intro k hk
      by_cases hkt : j k=t
      · rw [if_pos hkt,if_pos hkt,hDs i k (by omega),add_zero]
      · rw [if_neg hkt,if_neg hkt]
  · intro k hk hkN
    by_cases hkeq : j k=N+1
    · rw [hDb k hkeq]
      congr 1
      apply sum_congr rfl
      intro i hi
      rw [hB.support i k (Or.inr (by omega)),zero_add]
    · rw [hB.scalar k hk (by omega)]
      congr 1
      apply sum_congr rfl
      intro i hi
      rw [hDs i k hkeq,add_zero]
  · intro i k hi hk hik
    have hir : j i≠N+1 := by omega
    have hkr : j k≠N+1 := by omega
    rw [hDs i k hkr,hDs k i hir,add_zero,add_zero]
    by_cases heq : j i+j k=N+1
    · have h := hDsk i k hi hk heq
      simpa [degreeProductMatrix,hi,hk,heq,show j k+j i=N+1 by omega] using h
    · exact hB.skew i k hi hk (by omega)
  · intro i hi hii
    rw [hDs i i (by omega),add_zero]
    by_cases heq : j i+j i=N+1
    · have h := hDd i hi heq
      simpa [degreeProductMatrix,hi,heq] using h
    · exact hB.diagonal i hi (by omega)

/-- Finite induction assembles all exact rows into one coefficient matrix. -/
theorem exists_solved_coefficient_matrix
    (V : ℕ → Submodule K A) (a E : I → A) (j : I → ℕ)
    (c : ℕ → I → A) (N : ℕ)
    (hcV : ∀ t i,c t i∈V t) (hE : ∀ i,j i=0 → E i=0)
    (hrow : ∀ r,0<r → r≤N → (∑ i,a i*c r i)+
      (∑ i,if j i≤r then E i*c (r-j i) i else 0)=0)
    (hexact : ∀ r,0<r → r≤N → CoefficientRowExact V a E j r) :
    ∃ B : I → I → K,CoefficientRowsSolved a E j c N B := by
  induction N with
  | zero => exact ⟨0,coefficientRowsSolved_zero a E j c⟩
  | succ N ih =>
    obtain ⟨B,hB⟩ := ih (by intro r hr hrN; exact hrow r hr (by omega))
      (by intro r hr hrN; exact hexact r hr (by omega))
    exact hB.step V hcV hE (hrow (N+1) (by omega) le_rfl) (hexact (N+1) (by omega) le_rfl)

end Froberg
