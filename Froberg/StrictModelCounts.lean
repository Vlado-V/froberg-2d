import Froberg.StrictVectorModel
import Froberg.AttachedDimensionCounts

/-! Exact ordinary monomial counts for every strict vector model. -/
noncomputable section
namespace Froberg.VectorExpansionOpen
open Module Quartic VectorMultiplicationCoordinates
variable {K : Type*} [Field K] {h n s d c : ℕ} {G : ℝ}

lemma formCount_eq_choose (hn : 0 < n) : FormCount n d=(n+d-1).choose d := by
  rw [← AttachedMultiplication.forms_finrank_count (K := ℚ),finrank_forms ℚ n d hn]

lemma rowCount_eq_choose (hn : 0 < n) : RowCount h n s=h*(n+s-1).choose s := by
  rw [← rows_finrank (K := ℚ)]
  simp [Rows,Module.finrank_pi_fintype,finrank_forms ℚ n s hn]

lemma StrictModel.source_dimension_add {g : Fin c → Rows K h n s} (hg : StrictModel g d G) :
    finrank K (Source g)+c=RowCount h n s := by
  have hd := (Submodule.span K (Set.range g)).finrank_quotient_add_finrank
  simpa only [finrank_span_eq_card hg.independent,Fintype.card_fin,rows_finrank] using hd

lemma StrictModel.target_dimension_add {g : Fin c → Rows K h n s} (hg : StrictModel g d G) :
    finrank K (Target g d)+c*FormCount n d=RowCount h n (s+d) := by
  have hd := (BilinearImage.image (multiplication (d := d))
    (Submodule.span K (Set.range g))).finrank_quotient_add_finrank
  simpa only [product_span_dimension g hg.product_injective,rows_finrank] using hd

lemma StrictModel.source_real_count {g : Fin c → Rows K h n s} (hg : StrictModel g d G)
    (hn : 0 < n) : (finrank K (Source g) : ℝ)=(h : ℝ)*((n+s-1).choose s : ℝ)-c := by
  have hd := hg.source_dimension_add
  rw [rowCount_eq_choose hn] at hd
  have hdR : (finrank K (Source g) : ℝ)+c=(h : ℝ)*((n+s-1).choose s : ℝ) := by exact_mod_cast hd
  linarith

lemma StrictModel.target_real_count {g : Fin c → Rows K h n s} (hg : StrictModel g d G)
    (hn : 0 < n) : (finrank K (Target g d) : ℝ)=
      (h : ℝ)*((n+(s+d)-1).choose (s+d) : ℝ)-(c : ℝ)*((n+d-1).choose d : ℝ) := by
  have hd := hg.target_dimension_add
  rw [rowCount_eq_choose hn,formCount_eq_choose hn] at hd
  have hdR : (finrank K (Target g d) : ℝ)+(c : ℝ)*((n+d-1).choose d : ℝ)=
      (h : ℝ)*((n+(s+d)-1).choose (s+d) : ℝ) := by exact_mod_cast hd
  linarith

end Froberg.VectorExpansionOpen
