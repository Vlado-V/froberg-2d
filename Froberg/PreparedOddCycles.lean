module

public import Froberg.FullPreparedFibers
public import Froberg.PreparedEvenReduction
public import Froberg.DelayedOddElimination
public import Froberg.BiformParitySpaces

@[expose] public section

/-! The full odd source, including outer vectors and mixed pure generators,
has only cross-parity constant cycles once its first and higher linear
coefficient rows are exact. All prepared high parts and all pure forms
remain arbitrary. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def combinedLinear (P : OuterSpace K (Fin h) m d u) (F : OuterSpace K (Fin h) m d f) :
    Fin f ⊕ Fin u → MvPolynomial (Fin h ⊕ Fin m) K :=
  Sum.elim (fun i => (F i).val) (fun j => (P j).val)

def combinedPure (U : Fin u → Forms K h d) :
    Fin f ⊕ Fin u → MvPolynomial (Fin h ⊕ Fin m) K :=
  Sum.elim (fun _ => 0) (fun j => rename Sum.inl (U j).val)

def oddGenerator (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (F : OuterSpace K (Fin h) m d f) : Fin f ⊕ Fin u → MvPolynomial (Fin h ⊕ Fin m) K :=
  combinedLinear P F+combinedPure U

def OddCyclesExact (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (p : PreparedParameters.Space m d q J counts O × OuterSpace K (Fin h) m d f) : Prop :=
  ∀ (c : PreparedParameters.Label q J counts → MvPolynomial (Fin h ⊕ Fin m) K)
    (v : Fin f ⊕ Fin u → MvPolynomial (Fin h ⊕ Fin m) K),
    (∀ i,(c i).IsHomogeneous d) → (∀ k,(v k).IsHomogeneous d) →
    (∀ i α,(c i).coeff α≠0 → Finsupp.weight (blockWeight h m) α%2=1) →
    (∀ k α,(v k).coeff α≠0 → Finsupp.weight (blockWeight h m) α%2=0) →
    (∑ i,PreparedParameters.generator p.1 i*c i)+(∑ k,oddGenerator U P p.2 k*v k)=0 →
    ∃ B : PreparedParameters.Label q J counts → (Fin f ⊕ Fin u) → K,
      (∀ i,c i=∑ k,B i k • oddGenerator U P p.2 k) ∧
      (∀ k,v k = -∑ i,B i k • PreparedParameters.generator p.1 i)

theorem zero_scalar_odd_cycles_exact (hd : 3≤d) (hdodd : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (hpos : ∀ j∈J,0<j) (heven : ∀ j∈J,j%2=0)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (p : PreparedParameters.Space m d q J counts O × OuterSpace K (Fin h) m d f)
    (hfirst : ∀ (x : PreparedParameters.Label q J counts → MvPolynomial (Fin h ⊕ Fin m) K)
      (y : Fin f ⊕ Fin u → MvPolynomial (Fin h ⊕ Fin m) K),
      (∀ i,x i∈coefficientComponentSpace (blockWeight h m) d 1) →
      (∀ k,y k∈coefficientComponentSpace (blockWeight h m) d 0) →
      (∑ i,PreparedParameters.scalar p.1 i*x i)+(∑ k,combinedLinear P p.2 k*y k)=0 →
      ∃ B : PreparedParameters.Label q J counts → (Fin f ⊕ Fin u) → K,
        (∀ i,x i=∑ k,B i k • combinedLinear P p.2 k) ∧
        (∀ k,y k = -∑ i,B i k • PreparedParameters.scalar p.1 i))
    (hhigher : ∀ r,3≤r → r≤d+1 → r%2=1 →
      ∀ (x : PreparedParameters.Label q J counts → MvPolynomial (Fin h ⊕ Fin m) K)
        (y : Fin f ⊕ Fin u → MvPolynomial (Fin h ⊕ Fin m) K),
      (∀ i,x i∈coefficientComponentSpace (blockWeight h m) d r) →
      (∀ k,y k∈coefficientComponentSpace (blockWeight h m) d (r-1)) →
      (∑ i,PreparedParameters.scalar p.1 i*x i)+(∑ k,combinedLinear P p.2 k*y k)=0 →
      x=0 ∧ y=0) : OddCyclesExact U P p := by
  intro c v hc hv hcodd hveven hcycle
  apply delayed_odd_cycles (blockWeight h m) (by intro x; cases x <;> simp [blockWeight]) d hd
    (PreparedParameters.scalar p.1) (PreparedParameters.high p.1) c
    (combinedLinear P p.2) (combinedPure U) v PreparedParameters.degree
  · intro i
    refine ⟨(p.1.1 i).property.rename_isHomogeneous,?_⟩
    exact rename_weightedHomogeneous
      (⟨Sum.inr,Sum.inr_injective⟩ : Fin m ↪ Fin h ⊕ Fin m)
      (fun _ => 0) (blockWeight h m) (fun _ => rfl)
      (weightedHomogeneous_zero_weight (p.1.1 i).val)
  · intro i
    refine ⟨?_,PreparedParameters.high_weight hO p.1 i⟩
    cases i with
    | inl i => exact isHomogeneous_zero _ _ _
    | inr a =>
      have hh := biformImage_homogeneous _ _ (hO _ a.1.property) le_rfl (p.1.2 a.1 a.2).property
      change (p.1.2 a.1 a.2).val.IsHomogeneous (a.1.val+(d-a.1.val)) at hh
      simpa only [PreparedParameters.high,Sum.elim_inr,Nat.add_sub_of_le (hJ _ a.1.property)] using hh
  · intro i hi
    cases i with
    | inl i => rfl
    | inr a => have := hpos _ a.1.property; change a.1.val=0 at hi; omega
  · intro i
    cases i with
    | inl i => rfl
    | inr a => exact heven _ a.1.property
  · intro k
    have hlin (a : biformImage (Forms K h 1) (Forms K m (d-1))) :
        a.val.IsHomogeneous d ∧ a.val.IsWeightedHomogeneous (blockWeight h m) 1 := by
      refine ⟨?_,biformImage_output_weight _ _ le_rfl a.property⟩
      have hh := biformImage_homogeneous _ _ le_rfl le_rfl a.property
      change a.val.IsHomogeneous (1+(d-1)) at hh
      simpa only [show 1+(d-1)=d by omega] using hh
    cases k with
    | inl k => exact hlin (p.2 k)
    | inr k => exact hlin (P k)
  · intro k
    cases k with
    | inl k => exact ⟨isHomogeneous_zero _ _ _,(weightedHomogeneousSubmodule K _ _).zero_mem⟩
    | inr k =>
      refine ⟨(U k).property.rename_isHomogeneous,?_⟩
      exact rename_weightedHomogeneous
        (⟨Sum.inl,Sum.inl_injective⟩ : Fin h ↪ Fin h ⊕ Fin m)
        (fun _ => 1) (blockWeight h m) (fun _ => rfl) (U k).property
  · exact Or.inl hdodd
  · exact hc
  · exact hv
  · exact hcodd
  · exact hveven
  · exact hfirst
  · exact hhigher
  · exact hcycle

end Froberg.PreparedTarget
