module

public import Froberg.VectorFirstRowOpen

@[expose] public section

/-! Both the first exact row and all higher odd rows hold on one principal
open in the complete scalar/vector coefficient space. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Quartic VectorMultiplicationCoordinates
variable {K : Type} [Field K] [Infinite K] {h m d q f t : ℕ} {G : ℝ}

theorem scalar_vector_rows_open (hh : 0<h) (hm : 0 < m) (hd : 1≤d)
    (D : MvPolynomial (Fin (finrank K (Fin f → Rows K h m (d-1)))) K)
    (hD : ∃ g : Fin f → Rows K h m (d-1),eval ((Module.finBasis K _).equivFun g) D≠0)
    (hmodel : ∀ g : Fin f → Rows K h m (d-1),eval ((Module.finBasis K _).equivFun g) D≠0 →
      VectorExpansionOpen.StrictModel g d G ∧
      q*finrank K (VectorExpansionOpen.Source g)≤finrank K (VectorExpansionOpen.Target g d))
    (hscalar : HasOddScalarLayersOpen K h m d f q t)
    (hupper : (f+(h+d-1).choose d)*(h+d-1).choose d≤
      (h+(d+1)-1).choose (d+1)*(m+(d-1)-1).choose (d-1)) :
    ∃ P : MvPolynomial (Fin (finrank K (ScalarVectorParameters K h m d f q))) K,
      (∃ p : ScalarVectorParameters K h m d f q,eval ((Module.finBasis K _).equivFun p) P≠0) ∧
      ∀ p : ScalarVectorParameters K h m d f q,eval ((Module.finBasis K _).equivFun p) P≠0 →
        FirstVectorRowExact p.2 p.1 ∧ HigherOddRows p.2 p.1 := by
  obtain ⟨P,hP,hgood⟩ := higher_odd_vector_open hh hm hd hscalar hupper
  obtain ⟨g,Q,hg,hQ,hjoint⟩ := VectorExpansionOpen.strict_scalar_joint_selection D hD hmodel P hP
  obtain ⟨E,hE,hEgood⟩ := first_vector_row_open (g,Q)
    (firstVectorRowExact_of_quotient Q g hg.product_injective hQ)
  refine ⟨E*P,⟨(g,Q),by simpa only [map_mul] using mul_ne_zero hE hjoint⟩,?_⟩
  intro p hp
  have hps := mul_ne_zero_iff.mp (show eval ((Module.finBasis K _).equivFun p) E*
      eval ((Module.finBasis K _).equivFun p) P≠0 by simpa only [map_mul] using hp)
  exact ⟨hEgood p hps.1,hgood p hps.2⟩

end Froberg
