import Froberg.BiformOutputConstraint
import Froberg.BinomialParityMargin
import Froberg.NormalizedLimits

/-! The actual odd-half-degree output space used for a new even layer. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Finset
variable {K : Type} [Field K] [Infinite K]

def halfVariableEquiv (A : Type*) : (A ⊕ A) ≃ A × Bool where
  toFun := Sum.elim (fun x => (x,true)) (fun x => (x,false))
  invFun := fun x => if x.2 then Sum.inl x.1 else Sum.inr x.1
  left_inv := by rintro (x|x) <;> rfl
  right_inv := by rintro ⟨x,b⟩; cases b <;> rfl

def pairedHalfWeight {A : Type*} (x : A × Bool) : ℕ := if x.2 then 1 else 0

def OddOutputProfile (R : ℕ) := {a : Fin (R+1) // a.val%2=1}
instance (R : ℕ) : Fintype (OddOutputProfile R) := by unfold OddOutputProfile; infer_instance

def oddOutputDimension (w R : ℕ) : ℕ :=
  ∑ a : OddOutputProfile R, (w+a.val.val-1).choose a.val.val *
    (w+(R-a.val.val)-1).choose (R-a.val.val)

private def oddOutputFamily (w R : ℕ) :
    (Σ a : OddOutputProfile R, Sym (Fin w) a.val.val × Sym (Fin w) (R-a.val.val)) →
      MvPolynomial (Fin w × Bool) K := fun x =>
  rename (halfVariableEquiv (Fin w))
    (rename Sum.inl (formsBasis K w x.1.val.val x.2.1).val *
      rename Sum.inr (formsBasis K w (R-x.1.val.val) x.2.2).val)

private theorem oddOutputFamily_weighted (w R : ℕ) (a : OddOutputProfile R)
    (c : Sym (Fin w) a.val.val × Sym (Fin w) (R-a.val.val)) :
    (oddOutputFamily (K := K) w R ⟨a,c⟩).IsWeightedHomogeneous pairedHalfWeight a.val.val := by
  apply rename_weightedHomogeneous
    (halfVariableEquiv (Fin w)).toEmbedding FourBlocks.outputWeight pairedHalfWeight
  · rintro (x|x) <;> rfl
  · apply biformImage_output_weight (Forms K w a.val.val) (Forms K w (R-a.val.val)) le_rfl
    exact mul_mem_biformImage _ _ (formsBasis K w a.val.val c.1).property
      (formsBasis K w (R-a.val.val) c.2).property

private theorem oddOutputFamily_independent (w R : ℕ) :
    LinearIndependent K (oddOutputFamily (K := K) w R) := by
  apply linearIndependent_weighted_fibers pairedHalfWeight
    (fun a : OddOutputProfile R => a.val.val)
    (fun _ _ h => Subtype.ext (Fin.ext h)) (fun a c => oddOutputFamily w R ⟨a,c⟩)
  · intro a
    have hl := (formsBasis K w a.val.val).linearIndependent.map'
      (Forms K w a.val.val).subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have hr := (formsBasis K w (R-a.val.val)).linearIndependent.map'
      (Forms K w (R-a.val.val)).subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    exact (linearIndependent_cross_products_disjoint _ _ hl hr).map'
      (rename (halfVariableEquiv (Fin w))).toLinearMap
      (LinearMap.ker_eq_bot.mpr (rename_injective _ (halfVariableEquiv (Fin w)).injective))
  · exact oddOutputFamily_weighted w R

/-- A concrete output space has every odd half-degree, its exact dimension,
and no even-half-degree coefficient. -/
theorem exists_odd_output_space (w R : ℕ) :
    ∃ O : Submodule K (MvPolynomial (Fin w × Bool) K),
      O ≤ homogeneousSubmodule (Fin w × Bool) K R ∧
      finrank K O = oddOutputDimension w R ∧
      O ≤ (retainMonomials (fun a => Finsupp.weight pairedHalfWeight a % 2=0)).ker := by
  let O := Submodule.span K (Set.range (oddOutputFamily (K := K) w R))
  refine ⟨O,?_,?_,?_⟩
  · apply Submodule.span_le.mpr
    rintro f ⟨⟨a,⟨i,j⟩⟩,rfl⟩
    have h : (oddOutputFamily (K := K) w R ⟨a,⟨i,j⟩⟩).IsHomogeneous
        (a.val.val+(R-a.val.val)) := by
      apply IsHomogeneous.rename_isHomogeneous
      exact (formsBasis K w a.val.val i).property.rename_isHomogeneous.mul
        (formsBasis K w (R-a.val.val) j).property.rename_isHomogeneous
    have ha : a.val.val≤R := by have := a.val.isLt; omega
    change (oddOutputFamily (K := K) w R ⟨a,⟨i,j⟩⟩).IsHomogeneous R
    simpa only [Nat.add_sub_of_le ha] using h
  · rw [show O=Submodule.span K (Set.range (oddOutputFamily (K := K) w R)) from rfl,
      finrank_span_eq_card (oddOutputFamily_independent w R),Fintype.card_sigma]
    apply sum_congr rfl
    intro a ha
    rw [Fintype.card_prod]
    simp only [Sym.card_sym_eq_choose,Fintype.card_fin]
  · apply Submodule.span_le.mpr
    rintro f ⟨⟨a,c⟩,rfl⟩
    change retainMonomials _ (oddOutputFamily w R ⟨a,c⟩)=0
    ext α
    rw [coeff_retainMonomials]
    split_ifs with hα
    · by_contra hc
      have h := oddOutputFamily_weighted (K := K) w R a c hc
      have ha := a.property
      omega
    · rfl

end Froberg
