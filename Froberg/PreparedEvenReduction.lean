import Froberg.PreparedCoefficientRows
import Froberg.EmptyCoefficientRows
import Froberg.EvenParityElimination

/-! The exact actual even-cycle reduction in a prepared scalar/even family.
Only rows up to d need mixed scalar equations; larger rows need products. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

/-- Positive even labels carry no hidden scalar component. -/
theorem high_weight (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (p : Space n d q J counts O) (i : Label q J counts) :
    (high p i).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) (degree i) := by
  cases i with
  | inl i => exact (weightedHomogeneousSubmodule K _ _).zero_mem
  | inr a => exact biformImage_output_weight _ _ (hO _ a.1.property) (p.2 a.1 a.2).property

/-- All positive even polynomial components of a relation can be removed by
literal constant Koszul boundaries in the same prepared family. -/
theorem even_positive_rows_reduce_to_scalar
    [LinearOrder (Label q J counts)]
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (hpos : ∀ j∈J,0<j) (heven : ∀ j∈J,j%2=0)
    (hcover : ∀ r,0<r → r≤d → r%2=0 → r∈J)
    (p : Space n d q J counts O)
    (hrows : ∀ R : J,(row hO R p).ker=(rowConstants hO R p).range)
    (hproducts : ∀ R,d<R → R≤2*d → R%2=0 →
      Function.Injective (ProductRows.multiplication counts (layers p) J R))
    (c : Label q J counts → MvPolynomial (σ ⊕ Fin n) K)
    (hc : ∀ i,(c i).IsHomogeneous d)
    (hceven : ∀ i α,(c i).coeff α≠0 →
      Finsupp.weight (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) α%2=0)
    (hpositive : ∀ r,0<r → r≤2*d →
      weightedHomogeneousComponent (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) r
        (∑ i,generator p i*c i)=0) :
    ∃ (M : Label q J counts → Label q J counts → K)
      (z : Label q J counts → MvPolynomial (σ ⊕ Fin n) K),
      c-matrixBoundary (generator p) M=z ∧
      (∀ i,0<degree i → z i=0) ∧
      (∀ i,(z i).IsHomogeneous d ∧ (z i).IsWeightedHomogeneous
        (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) 0) := by
  let w := Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)
  have hw : ∀ x,w x≤1 := by intro x; cases x <;> simp [w]
  have hdeg : ∀ i : Label q J counts,degree i≤d := by
    intro i
    cases i with
    | inl i => exact Nat.zero_le _
    | inr a => exact hJ _ a.1.property
  have hzero : ∀ i : Label q J counts,degree i=0 → high p i=0 := by
    intro i hi
    cases i with
    | inl i => rfl
    | inr a => have := hpos _ a.1.property; change a.1.val=0 at hi; omega
  have hcover' (i : Label q J counts) (hi : 0<degree i) :
      ∃ a : ProductRows.LayerLabel J counts,Sum.inr a=i := by
    cases i with
    | inl i => exact False.elim (by change 0<0 at hi; omega)
    | inr a => exact ⟨a,rfl⟩
  apply polynomial_even_positive_rows_reduce_to_scalar w hw d (scalar p) (high p) c degree
  · intro i
    refine ⟨(p.1 i).property.rename_isHomogeneous,?_⟩
    exact rename_weightedHomogeneous
      (⟨Sum.inr,Sum.inr_injective⟩ : Fin n ↪ σ ⊕ Fin n)
      (fun _ => 0) w (fun _ => rfl) (weightedHomogeneous_zero_weight (p.1 i).val)
  · exact high_weight hO p
  · exact hzero
  · exact hdeg
  · intro i
    cases i with
    | inl i => rfl
    | inr a => exact heven _ a.1.property
  · exact hc
  · exact hceven
  · exact hpositive
  · intro R hR hRd hRe
    by_cases hle : R≤d
    · exact coefficient_row_of_exact hO hJ hpos ⟨R,hcover R hR hle hRe⟩ p (hrows _)
    · exact coefficient_row_above_degree w hw (by omega) (scalar p) (high p) degree hdeg
        (ProductRows.prepared_pair_independence (layers p) degree Sum.inr
          Sum.inr_injective (fun _ => rfl) hpos hcover' (high p)
          (fun a => (layers_active p a).symm) R (hproducts R (by omega) hRd hRe))

end Froberg.PreparedParameters
