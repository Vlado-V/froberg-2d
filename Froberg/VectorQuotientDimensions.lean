import Froberg.VectorQuotientOpen

/-! Exact dimensions in the actual polynomial quotients used by the open family. -/
noncomputable section
namespace Froberg.VectorExpansionOpen
open Module VectorMultiplicationCoordinates Quartic
variable {K : Type*} [Field K] {h n s d c : ℕ}

lemma rows_finrank : finrank K (Rows K h n s)=RowCount h n s := by
  calc
    _=finrank K (Fin (RowCount h n s) → K) := rowFiniteEquiv.finrank_eq
    _=RowCount h n s := by simp

lemma source_quotient_dimension (g : Fin c → Rows K h n s) (hg : LinearIndependent K g) :
    finrank K ((Rows K h n s) ⧸ Submodule.span K (Set.range g))=RowCount h n s-c := by
  have hd := (Submodule.span K (Set.range g)).finrank_quotient_add_finrank
  rw [finrank_span_eq_card hg,Fintype.card_fin,rows_finrank] at hd
  omega

lemma target_quotient_dimension (g : Fin c → Rows K h n s)
    (hg : Function.Injective (BilinearImage.tupleMap (multiplication (d := d)) g)) :
    finrank K ((Rows K h n (s+d)) ⧸ BilinearImage.image (multiplication (d := d))
      (Submodule.span K (Set.range g)))=RowCount h n (s+d)-c*FormCount n d := by
  have hd := (BilinearImage.image (multiplication (d := d))
    (Submodule.span K (Set.range g))).finrank_quotient_add_finrank
  rw [product_span_dimension g hg,rows_finrank] at hd
  omega

end Froberg.VectorExpansionOpen
