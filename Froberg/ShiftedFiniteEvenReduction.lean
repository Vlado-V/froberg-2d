module

public import Froberg.ExtendedEvenRowWitnesses
public import Froberg.PreparedPrivateFinite
public import Froberg.PreparedFiniteEvenReduction

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
theorem finite_even_reduction_open_shift {w v z d q : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    [LinearOrder (Label q J counts)]
    (hd : 3≤d) (hv : 0<v)
    (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X)
    (hJ : ∀ j∈J,2≤j) (hdegree : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (h2 : 2∈J) (hcover : ∀ r,0<r → r≤d → r%2=0 → r∈J)
    (hquad : ∃ b,QuadraticRowCapacity (v+v) d q b J counts (constrainedOutputs T))
    (hhigher : ∀ R : J,R.val≠2 → ∃ b,HigherRowCapacity w v d q b J counts T R)
    (hproduct : ∀ R,d<R → R≤2*d → R%2=0 →
      ProductRowCapacity (K := K) (X := X) w v d R J counts) :
    let S := Space (v+v+z) d q J counts (constrainedOutputs T)
    ∃ D : MvPolynomial (Fin (finrank K S)) K,
      (∃ p : S,eval ((Module.finBasis K S).equivFun p) D≠0) ∧
      ∀ p : S,eval ((Module.finBasis K S).equivFun p) D≠0 →
        ∀ c : Label q J counts → MvPolynomial ((Fin w × Bool) ⊕ Fin (v+v+z)) K,
          (∀ i,(c i).IsHomogeneous d) →
          (∀ i α,(c i).coeff α≠0 →
            Finsupp.weight (Sum.elim (fun _ : Fin w × Bool => 1) (fun _ : Fin (v+v+z) => 0)) α%2=0) →
          (∀ r,0<r → r≤2*d → weightedHomogeneousComponent
            (Sum.elim (fun _ : Fin w × Bool => 1) (fun _ : Fin (v+v+z) => 0)) r
            (∑ i,generator p i*c i)=0) →
          ∃ (M : Label q J counts → Label q J counts → K)
            (rem : Label q J counts → MvPolynomial ((Fin w × Bool) ⊕ Fin (v+v+z)) K),
            c-matrixBoundary (generator p) M=rem ∧
            (∀ i,0<degree i → rem i=0) ∧
            (∀ i,(rem i).IsHomogeneous d ∧ (rem i).IsWeightedHomogeneous
              (Sum.elim (fun _ : Fin w × Bool => 1) (fun _ : Fin (v+v+z) => 0)) 0) := by
  classical
  let S := Space (v+v+z) d q J counts (constrainedOutputs T)
  let B := (Finset.range (2*d+1)).filter (fun R => d<R ∧ R%2=0)
  have hB (R : ℕ) : R∈B ↔ d<R ∧ R≤2*d ∧ R%2=0 := by simp only [B,Finset.mem_filter,Finset.mem_range]; omega
  obtain ⟨ell,hell⟩ := exists_two_core_linear_forms (K := K) (by omega : 2≤v+v)
  have hwit : ∀ R : J,∃ p : S,
      LinearIndependent K (fun i => intrinsicLayerMap (fun _ _ => inf_le_left) R i p) ∧
      (row (fun _ _ => inf_le_left) R p).ker=(rowConstants (fun _ _ => inf_le_left) R p).range := by
    intro R
    by_cases hR : R.val=2
    · have hReq : R=(⟨2,h2⟩ : J) := Subtype.ext hR
      subst R
      obtain ⟨b,hb⟩ := hquad
      exact exists_quadratic_extended_row_parameter hd (fun _ _ => inf_le_left)
        hJ hdegree h2 hb ell hell
    · obtain ⟨b,hb⟩ := hhigher R hR
      exact exists_higher_extended_row_parameter R hb ell hell
  obtain ⟨D₁,hD₁,hgood₁⟩ := rows_common_open (O := constrainedOutputs T)
    (fun _ _ => inf_le_left) hdegree hwit
  obtain ⟨D₂,hD₂,hgood₂⟩ := products_common_open (n := v+v+z) (q := q) (O := constrainedOutputs T)
    (fun _ _ => inf_le_left) hdegree B (by
      intro R hR
      obtain ⟨hRd,hR2d,hRe⟩ := (hB R).mp hR
      obtain ⟨p,hp⟩ := exists_product_row_parameter (q := q) T (hproduct R hRd hR2d hRe)
      exact ⟨coreExtension z p,private_product_extension p hp⟩)
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
