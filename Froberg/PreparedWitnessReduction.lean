import Froberg.PreparedActualReduction

/-! Actual row and product witnesses, of any construction, produce the
same positive even-relation reduction on the full parameter space. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem even_reduction_open_of_witnesses
    [Module.Finite K (Space n d q J counts O)] [LinearOrder (Label q J counts)]
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,2≤j) (hdegree : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hcover : ∀ r,0<r → r≤d → r%2=0 → r∈J)
    (hrows : ∀ R : J,∃ p : Space n d q J counts O,
      LinearIndependent K (fun i => intrinsicLayerMap hO R i p) ∧
      (row hO R p).ker=(rowConstants hO R p).range)
    (hproducts : ∀ R,d<R → R≤2*d → R%2=0 →
      ∃ p : Space n d q J counts O,
        Function.Injective (ProductRows.multiplication counts (layers p) J R)) :
    ∃ D : MvPolynomial (Fin (finrank K (Space n d q J counts O))) K,
      (∃ p : Space n d q J counts O,eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p : Space n d q J counts O,eval ((Module.finBasis K _).equivFun p) D≠0 →
        EvenPositiveReduction p := by
  classical
  let S := Space n d q J counts O
  let B := (Finset.range (2*d+1)).filter (fun R => d<R ∧ R%2=0)
  have hB (R : ℕ) : R∈B ↔ d<R ∧ R≤2*d ∧ R%2=0 := by simp only [B,Finset.mem_filter,Finset.mem_range]; omega
  obtain ⟨D₁,hD₁,hgood₁⟩ := rows_common_open hO hdegree hrows
  obtain ⟨D₂,hD₂,hgood₂⟩ := products_common_open (n := n) (q := q) (O := O)
    hO hdegree B (by
      intro R hR
      obtain ⟨hRd,hR2d,hRe⟩ := (hB R).mp hR
      exact hproducts R hRd hR2d hRe)
  have hx₁ : ∃ x,eval x D₁≠0 := by obtain ⟨p,hp⟩ := hD₁; exact ⟨(Module.finBasis K S).equivFun p,hp⟩
  have hx₂ : ∃ x,eval x D₂≠0 := by obtain ⟨p,hp⟩ := hD₂; exact ⟨(Module.finBasis K S).equivFun p,hp⟩
  obtain ⟨x,hx1,hx2⟩ := principal_opens_intersect hx₁ hx₂
  refine ⟨D₁*D₂,⟨(Module.finBasis K S).equivFun.symm x,?_⟩,?_⟩
  · simpa only [S,LinearEquiv.apply_symm_apply,map_mul] using mul_ne_zero hx1 hx2
  intro p hp c hc hceven hpositive
  have hps : eval ((Module.finBasis K S).equivFun p) D₁≠0 ∧
      eval ((Module.finBasis K S).equivFun p) D₂≠0 := by
    simpa only [map_mul,mul_ne_zero_iff] using hp
  exact even_positive_rows_reduce_to_scalar (O := O) hO hdegree
    (fun j hj => lt_of_lt_of_le (by decide : 0<2) (hJ j hj)) heven hcover p
    (hgood₁ p hps.1) (fun R hRd hR2d hRe => hgood₂ p hps.2 R ((hB R).mpr ⟨hRd,hR2d,hRe⟩))
    c hc hceven hpositive


end Froberg.PreparedParameters
