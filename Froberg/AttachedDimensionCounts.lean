module

public import Froberg.AttachedReindex
public import Froberg.VectorQuotientDimensions

@[expose] public section

/-! Field-independent monomial counts for the actual attached quotients. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open Module VectorMultiplicationCoordinates Quartic
variable {K I : Type*} [Field K] [Fintype I] {h n s d : ℕ}

lemma forms_finrank_count : finrank K (Forms K n d)=FormCount n d := by
  calc
    _=finrank K (Fin (FormCount n d) → K) := HomogeneousCoefficientCoordinates.finiteEquiv.finrank_eq
    _=FormCount n d := by simp

lemma relation_dimension_count (e : I → Fin n →₀ ℕ) (v : I → Fin h → K)
    (he : ∀ i,(e i).degree=s) (hi : Function.Injective (AttachedMultiplication.multiplication (d := d) e v)) :
    finrank K (relationSpace (d := d) e v he)=Fintype.card I*FormCount n d := by
  change finrank K (LinearMap.range (homogeneousMultiplication (d := d) e v he))=_
  rw [LinearMap.finrank_range_of_inj (homogeneousMultiplication_injective e v he hi)]
  simp [Module.finrank_pi_fintype,forms_finrank_count]

lemma attached_quotient_dimension_count (e : I → Fin n →₀ ℕ) (v : I → Fin h → K)
    (he : ∀ i,(e i).degree=s) (hi : Function.Injective (AttachedMultiplication.multiplication (d := d) e v)) :
    finrank K ((Fin h → Forms K n (s+d)) ⧸ relationSpace (d := d) e v he)=
      RowCount h n (s+d)-Fintype.card I*FormCount n d := by
  have hd := (relationSpace (d := d) e v he).finrank_quotient_add_finrank
  rw [relation_dimension_count e v he hi,VectorExpansionOpen.rows_finrank] at hd
  omega

lemma formCount_zero (hn : 0 < n) : FormCount n 0=1 := by
  rw [← forms_finrank_count (K := ℚ),finrank_forms ℚ n 0 hn]
  simp

lemma attached_source_dimension_count (e : I → Fin n →₀ ℕ) (v : I → Fin h → K)
    (he : ∀ i,(e i).degree=s) (hn : 0 < n)
    (hi : Function.Injective (AttachedMultiplication.multiplication (d := 0) e v)) :
    finrank K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)=
      RowCount h n s-Fintype.card I := by
  simpa only [Nat.add_zero,formCount_zero hn,mul_one] using attached_quotient_dimension_count e v he hi

end Froberg.AttachedMultiplication
