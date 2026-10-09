module

public import Froberg.PreparedPrivateFirstComponent
public import Froberg.PreparedPrivateCoefficientRows
public import Froberg.PreparedPrivateTopCoefficient
public import Froberg.PrivateCompleteElimination

@[expose] public section

/-! The checked row conditions on one actual prepared parameter yield the
full odd-degree even-cycle reduction, uniformly in its fixed pure U tuple. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q b : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem private_prepared_positive_reduction [LinearOrder (Label q J counts)]
    (hd : 3≤d) (hodd : d%2=1)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (hmin : ∀ j∈J,2≤j) (heven : ∀ j∈J,j%2=0)
    (hcover : ∀ r,0<r → r≤d → r%2=0 → r∈J)
    (p : Space n d q J counts O) (P : Fin b → FullBiform K σ n 1 (d-1))
    (U : Fin b → MvPolynomial (σ ⊕ Fin n) K)
    (hU : ∀ i,(U i).IsHomogeneous d ∧
      (U i).IsWeightedHomogeneous (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) d)
    (hrows : ∀ R : J,(privateAugmentedRow hO R p (fun i => (P i).val)).ker=
      ((rowConstants hO R p).prodMap (privateBoundaryAt P R.val)).range)
    (hproducts : ∀ R,d<R → R≤2*d → R%2=0 →
      Function.Injective (ProductRows.multiplication counts (layers p) J R))
    (htop : Function.Injective (privateTopRow p (fun i => (P i).val)))
    (c : Label q J counts → MvPolynomial (σ ⊕ Fin n) K)
    (v : Fin b → MvPolynomial (σ ⊕ Fin n) K)
    (hc : ∀ i,(c i).IsHomogeneous d) (hv : ∀ i,(v i).IsHomogeneous d)
    (hceven : ∀ i α,(c i).coeff α≠0 → Finsupp.weight
      (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) α%2=0)
    (hvodd : ∀ i α,(v i).coeff α≠0 → Finsupp.weight
      (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) α%2=1)
    (hpositive : ∀ r,0<r → r≤2*d → weightedHomogeneousComponent
      (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) r
        ((∑ i,generator p i*c i)+(∑ k,((P k).val+U k)*v k))=0) :
    ∃ (C : Fin b → Fin b → K) (M : Label q J counts → Label q J counts → K)
      (z : Label q J counts → MvPolynomial (σ ⊕ Fin n) K),
      v=matrixBoundary (fun k => (P k).val+U k) C ∧ c-matrixBoundary (generator p) M=z ∧
      (∀ i,0<degree i → z i=0) ∧
      (∀ i,(z i).IsHomogeneous d ∧ (z i).IsWeightedHomogeneous
        (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) 0) := by
  let w := Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)
  have hw : ∀ x,w x≤1 := by intro x; cases x <;> simp [w]
  have hpos : ∀ j∈J,0<j := fun j hj => by have := hmin j hj; omega
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
  have hexact : ∀ r,0<r → r≤2*d → r%2=0 →
      CoefficientRowExact (coefficientComponentSpace w d) (scalar p) (high p) degree r := by
    intro R hR hRd hRe
    by_cases hle : R≤d
    · exact coefficient_row_of_exact hO hJ hpos ⟨R,hcover R hR hle hRe⟩ p
        (private_row_ordinary_exact hO _ p P (hrows _))
    · exact coefficient_row_above_degree w hw (by omega) (scalar p) (high p) degree hdeg
        (ProductRows.prepared_pair_independence (layers p) degree Sum.inr
          Sum.inr_injective (fun _ => rfl) hpos hcover' (high p)
          (fun a => (layers_active p a).symm) R (hproducts R (by omega) hRd hRe))
  have hsep : ∀ r,3≤r → r≤2*d → r%2=0 →
      PrivateRowSeparation (coefficientComponentSpace w d) (coefficientComponentSpace w d)
        (scalar p) (high p) (fun i => (P i).val) degree r := by
    intro R hR hRd hRe
    by_cases hle : R≤d
    · exact private_coefficient_row_of_separated hO hJ hpos
        ⟨R,hcover R (by omega) hle hRe⟩ p (fun i => (P i).val)
        (private_row_separated hO _ (by change R≠2; omega) p P (hrows _))
    · by_cases heq : R=d+1
      · subst R
        exact private_top_coefficient_separation hJ hpos p (fun i => (P i).val) htop
      · intro x f B u hx hf hu hB hrel
        funext i
        have hi := hu i
        rw [coefficientComponentSpace_above w hw (by omega : d<R-1)] at hi
        exact hi
  have h2 : 2∈J := hcover 2 (by omega) (by omega) rfl
  apply private_complete_positive_reduction w hw d hd hodd (scalar p) (high p) c
    (fun i => (P i).val) U v degree
  · intro i
    exact ⟨(p.1 i).property.rename_isHomogeneous,
      rename_weightedHomogeneous (⟨Sum.inr,Sum.inr_injective⟩ : Fin n ↪ σ ⊕ Fin n)
        (fun _ => 0) w (fun _ => rfl) (weightedHomogeneous_zero_weight (p.1 i).val)⟩
  · exact high_weight hO p
  · intro i
    have hi := biformImage_homogeneous _ _ le_rfl le_rfl (P i).property
    refine ⟨?_,biformImage_output_weight _ _ le_rfl (P i).property⟩
    change (P i).val.IsHomogeneous (1+(d-1)) at hi
    simpa only [show 1+(d-1)=d by omega] using hi
  · exact hU
  · exact hzero
  · exact hdeg
  · intro i
    cases i with
    | inl i => rfl
    | inr a => exact heven _ a.1.property
  · exact hc
  · exact hv
  · exact hceven
  · exact hvodd
  · apply private_first_component_boundary hd hO hJ hmin h2 p P
      (by simpa only [privateBoundaryAt_two] using hrows ⟨2,h2⟩) U
      (fun i => (hU i).2) c v hc hv
    exact hpositive 2 (by omega) (by omega)
  · exact hpositive
  · exact hexact
  · exact hsep

end Froberg.PreparedParameters
