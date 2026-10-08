import Froberg.PreparedPrivateSelectedOpen
import Froberg.PreparedPrivateReduction
import Froberg.PreparedProductOpen

/-! A single open of actual prepared coefficients satisfies every private
row condition. The pure output tuple is arbitrary and remains fixed. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q b : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

/-- Every positive even relation in the private prepared family reduces to
scalar relations and actual constant alternating boundaries. -/
def PrivatePositiveReduction (p : Space n d q J counts O)
    (P : Fin b → FullBiform K σ n 1 (d-1)) : Prop :=
  ∀ U : Fin b → MvPolynomial (σ ⊕ Fin n) K,
    (∀ i,(U i).IsHomogeneous d ∧ (U i).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) d) →
  ∀ (c : Label q J counts → MvPolynomial (σ ⊕ Fin n) K)
    (v : Fin b → MvPolynomial (σ ⊕ Fin n) K),
    (∀ i,(c i).IsHomogeneous d) → (∀ i,(v i).IsHomogeneous d) →
    (∀ i α,(c i).coeff α≠0 → Finsupp.weight
      (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) α%2=0) →
    (∀ i α,(v i).coeff α≠0 → Finsupp.weight
      (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) α%2=1) →
    (∀ r,0<r → r≤2*d → weightedHomogeneousComponent
      (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) r
        ((∑ i,generator p i*c i)+(∑ k,((P k).val+U k)*v k))=0) →
    ∃ (C : Fin b → Fin b → K) (M : Label q J counts → Label q J counts → K)
      (z : Label q J counts → MvPolynomial (σ ⊕ Fin n) K),
      v=matrixBoundary (fun k => (P k).val+U k) C ∧ c-matrixBoundary (generator p) M=z ∧
      (∀ i,0<degree i → z i=0) ∧
      (∀ i,(z i).IsHomogeneous d ∧ (z i).IsWeightedHomogeneous
        (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) 0)

theorem private_reduction_open_of_witnesses
    [Module.Finite K (Space n d q J counts O)] [LinearOrder (Label q J counts)]
    (hd : 3≤d) (hodd : d%2=1)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,2≤j) (hdegree : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hcover : ∀ r,0<r → r≤d → r%2=0 → r∈J)
    (P : Fin b → FullBiform K σ n 1 (d-1))
    (hfirst : ∃ p : Space n d q J counts O,
      (privateAugmentedRow hO ⟨2,hcover 2 (by omega) (by omega) rfl⟩ p (fun i => (P i).val)).ker=
        ((rowConstants hO ⟨2,hcover 2 (by omega) (by omega) rfl⟩ p).prodMap (intrinsicPrivateBoundary P)).range)
    (hlater : ∀ R : J,R.val≠2 → ∃ p : Space n d q J counts O,
      (privateAugmentedRow hO R p (fun i => (P i).val)).ker=
        (privateAugmentedConstants (b := b) hO R p).range)
    (hproducts : ∀ R,d<R → R≤2*d → R%2=0 →
      ∃ p : Space n d q J counts O,
        Function.Injective (ProductRows.multiplication counts (layers p) J R))
    (htop : ∃ p : Space n d q J counts O,
      Function.Injective (privateTopRow p (fun i => (P i).val))) :
    ∃ D : MvPolynomial (Fin (finrank K (Space n d q J counts O))) K,
      (∃ p : Space n d q J counts O,eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p : Space n d q J counts O,eval ((Module.finBasis K _).equivFun p) D≠0 →
        PrivatePositiveReduction p P := by
  classical
  let S := Space n d q J counts O
  let B := (Finset.range (2*d+1)).filter (fun R => d<R ∧ R%2=0)
  have hB (R : ℕ) : R∈B ↔ d<R ∧ R≤2*d ∧ R%2=0 := by
    simp only [B,Finset.mem_filter,Finset.mem_range]; omega
  obtain ⟨D₁,hD₁,hgood₁⟩ := private_common_open_of_row_witnesses hO hdegree
    (hcover 2 (by omega) (by omega) rfl) P hfirst hlater
  obtain ⟨D₂,hD₂,hgood₂⟩ := products_common_open (n := n) (q := q) (O := O)
    hO hdegree B (by
      intro R hR
      obtain ⟨hRd,hR2d,hRe⟩ := (hB R).mp hR
      exact hproducts R hRd hR2d hRe)
  obtain ⟨p₃,hp₃⟩ := htop
  obtain ⟨D₃,hD₃,hgood₃⟩ := private_top_principal_open hO hdegree (fun i => (P i).val) p₃ hp₃
  have hx₁ : ∃ x,eval x D₁≠0 := by obtain ⟨p,hp⟩ := hD₁; exact ⟨(Module.finBasis K S).equivFun p,hp⟩
  have hx₂ : ∃ x,eval x D₂≠0 := by obtain ⟨p,hp⟩ := hD₂; exact ⟨(Module.finBasis K S).equivFun p,hp⟩
  obtain ⟨x,hx1,hx2⟩ := principal_opens_intersect hx₁ hx₂
  obtain ⟨y,hy12,hy3⟩ := principal_opens_intersect
    (show ∃ x,eval x (D₁*D₂)≠0 from ⟨x,by simpa only [map_mul] using mul_ne_zero hx1 hx2⟩)
    (show ∃ x,eval x D₃≠0 from ⟨(Module.finBasis K S).equivFun p₃,hD₃⟩)
  refine ⟨D₁*D₂*D₃,⟨(Module.finBasis K S).equivFun.symm y,?_⟩,?_⟩
  · simpa only [S,LinearEquiv.apply_symm_apply,map_mul] using mul_ne_zero hy12 hy3
  intro p hp U hU c v hc hv hceven hvodd hpositive
  have hps : (eval ((Module.finBasis K S).equivFun p) D₁≠0 ∧
      eval ((Module.finBasis K S).equivFun p) D₂≠0) ∧
      eval ((Module.finBasis K S).equivFun p) D₃≠0 := by
    simpa only [map_mul,mul_ne_zero_iff] using hp
  exact private_prepared_positive_reduction hd hodd hO hdegree hJ heven hcover p P U hU
    (hgood₁ p hps.1.1).1
    (fun R hRd hR2d hRe => hgood₂ p hps.1.2 R ((hB R).mpr ⟨hRd,hR2d,hRe⟩))
    (hgood₃ p hps.2) c v hc hv hceven hvodd hpositive

end Froberg.PreparedParameters
