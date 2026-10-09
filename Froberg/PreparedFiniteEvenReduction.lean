module

public import Froberg.PreparedRowsFromCapacities
public import Froberg.PreparedFiniteProducts

@[expose] public section

/-! A single finite-capacity constructor for the scalar/even prepared family.
The resulting open carries the literal positive-row boundary reduction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

/-- Finite row capacities produce one actual parameter open, on every point
of which all even positive-row relations reduce to the old scalar labels. -/
theorem finite_even_reduction_open {w v d q : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    [LinearOrder (Label q J counts)]
    (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X)
    (hJ : ∀ j∈J,2≤j) (hdegree : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (h2 : 2∈J) (hcover : ∀ r,0<r → r≤d → r%2=0 → r∈J)
    (hquad : ∃ b,QuadraticRowCapacity (v+v) d q b J counts (constrainedOutputs T))
    (hhigher : ∀ R : J,R.val≠2 → ∃ b,HigherRowCapacity w v d q b J counts T R)
    (hproduct : ∀ R,d<R → R≤2*d → R%2=0 →
      ProductRowCapacity (K := K) (X := X) w v d R J counts) :
    let S := Space (v+v) d q J counts (constrainedOutputs T)
    ∃ D : MvPolynomial (Fin (finrank K S)) K,
      (∃ p : S,eval ((Module.finBasis K S).equivFun p) D≠0) ∧
      ∀ p : S,eval ((Module.finBasis K S).equivFun p) D≠0 →
        ∀ c : Label q J counts → MvPolynomial ((Fin w × Bool) ⊕ Fin (v+v)) K,
          (∀ i,(c i).IsHomogeneous d) →
          (∀ i α,(c i).coeff α≠0 →
            Finsupp.weight (Sum.elim (fun _ : Fin w × Bool => 1) (fun _ : Fin (v+v) => 0)) α%2=0) →
          (∀ r,0<r → r≤2*d → weightedHomogeneousComponent
            (Sum.elim (fun _ : Fin w × Bool => 1) (fun _ : Fin (v+v) => 0)) r
            (∑ i,generator p i*c i)=0) →
          ∃ (M : Label q J counts → Label q J counts → K)
            (z : Label q J counts → MvPolynomial ((Fin w × Bool) ⊕ Fin (v+v)) K),
            c-matrixBoundary (generator p) M=z ∧
            (∀ i,0<degree i → z i=0) ∧
            (∀ i,(z i).IsHomogeneous d ∧ (z i).IsWeightedHomogeneous
              (Sum.elim (fun _ : Fin w × Bool => 1) (fun _ : Fin (v+v) => 0)) 0) := by
  classical
  let S := Space (v+v) d q J counts (constrainedOutputs T)
  let B := (Finset.range (2*d+1)).filter (fun R => d<R ∧ R%2=0)
  have hB (R : ℕ) : R∈B ↔ d<R ∧ R≤2*d ∧ R%2=0 := by simp only [B,Finset.mem_filter,Finset.mem_range]; omega
  obtain ⟨D₁,hD₁,hgood₁⟩ := rows_open_of_capacities T hJ hdegree h2 hquad hhigher
  obtain ⟨D₂,hD₂,hgood₂⟩ := products_common_open (n := v+v) (q := q) (O := constrainedOutputs T)
    (fun _ _ => inf_le_left) hdegree B (by
      intro R hR
      obtain ⟨hRd,hR2d,hRe⟩ := (hB R).mp hR
      exact exists_product_row_parameter T (hproduct R hRd hR2d hRe))
  have hx₁ : ∃ x,eval x D₁≠0 := by obtain ⟨p,hp⟩ := hD₁; exact ⟨(Module.finBasis K S).equivFun p,hp⟩
  have hx₂ : ∃ x,eval x D₂≠0 := by obtain ⟨p,hp⟩ := hD₂; exact ⟨(Module.finBasis K S).equivFun p,hp⟩
  obtain ⟨x,hx1,hx2⟩ := principal_opens_intersect hx₁ hx₂
  refine ⟨D₁*D₂,⟨(Module.finBasis K S).equivFun.symm x,?_⟩,?_⟩
  · simpa only [S,LinearEquiv.apply_symm_apply,map_mul] using mul_ne_zero hx1 hx2
  intro p hp c hc hceven hpositive
  have hps : eval ((Module.finBasis K S).equivFun p) D₁≠0 ∧
      eval ((Module.finBasis K S).equivFun p) D₂≠0 := by
    simpa only [map_mul,mul_ne_zero_iff] using hp
  exact even_positive_rows_reduce_to_scalar (O := constrainedOutputs T) (fun _ _ => inf_le_left) hdegree
    (fun j hj => lt_of_lt_of_le (by decide : 0<2) (hJ j hj)) heven hcover p
    (hgood₁ p hps.1) (fun R hRd hR2d hRe => hgood₂ p hps.2 R ((hB R).mpr ⟨hRd,hR2d,hRe⟩))
    c hc hceven hpositive

end Froberg.PreparedParameters
