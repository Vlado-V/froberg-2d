module

public import Froberg.PreparedCountRestriction
public import Froberg.PreparedScalarFiberAt

@[expose] public section

/-! Vary only the old positive scalar slots of an enlarged prepared
family. Every added scalar slot and every high term stays fixed. -/
noncomputable section
set_option maxHeartbeats 150000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {c c' : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

/-- The second input stores the fixed enlarged family; its old positive
scalar values are ignored and replaced by the first input. -/
def countScalarFiberLinear (_hc : ∀ j ∈ J, c j ≤ c' j) :
    PositiveScalars (K := K) m d J c × Space m d q J c' O →ₗ[K] Space m d q J c' O where
  toFun x :=
    (Sum.elim (fun i => x.2.1 (Sum.inl i)) (fun a =>
      if hi : a.2.val < c a.1.val then
        x.1 ((Fintype.equivFin (ProductRows.LayerLabel J c)) ⟨a.1,⟨a.2.val,hi⟩⟩)
      else x.2.1 (Sum.inr a)),x.2.2)
  map_add' x y := by
    apply Prod.ext
    · funext i
      cases i with
      | inl i => rfl
      | inr a =>
        dsimp
        split_ifs <;> rfl
    · rfl
  map_smul' t x := by
    apply Prod.ext
    · funext i
      cases i with
      | inl i => rfl
      | inr a =>
        dsimp
        split_ifs <;> rfl
    · rfl

@[simp] theorem countScalarFiberLinear_base (hc : ∀ j ∈ J, c j ≤ c' j)
    (a : PositiveScalars (K := K) m d J c) (p : Space m d q J c' O) (i : Fin q) :
    (countScalarFiberLinear hc (a,p)).1 (Sum.inl i)=p.1 (Sum.inl i) := rfl

@[simp] theorem countScalarFiberLinear_high (hc : ∀ j ∈ J, c j ≤ c' j)
    (a : PositiveScalars (K := K) m d J c) (p : Space m d q J c' O) :
    (countScalarFiberLinear hc (a,p)).2=p.2 := rfl

theorem countScalarFiberLinear_old (hc : ∀ j ∈ J, c j ≤ c' j)
    (a : PositiveScalars (K := K) m d J c) (p : Space m d q J c' O)
    (i : ProductRows.LayerLabel J c) :
    (countScalarFiberLinear hc (a,p)).1 (Sum.inr (countLayerMap hc i))=
      a ((Fintype.equivFin _) i) := by
  rcases i with ⟨j,i⟩
  simp only [countScalarFiberLinear,LinearMap.coe_mk,AddHom.coe_mk,countLayerMap,
    Sum.elim_inr,Fin.val_castLE,dite_eq_left i.isLt]

theorem countScalarFiberLinear_extra (hc : ∀ j ∈ J, c j ≤ c' j)
    (a : PositiveScalars (K := K) m d J c) (p : Space m d q J c' O)
    (j : J) (i : Fin (c' j.val)) (hi : c j.val ≤ i.val) :
    (countScalarFiberLinear hc (a,p)).1 (Sum.inr ⟨j,i⟩)=p.1 (Sum.inr ⟨j,i⟩) := by
  simp only [countScalarFiberLinear,LinearMap.coe_mk,AddHom.coe_mk,Sum.elim_inr,
    dite_eq_right (not_lt.mpr hi)]

theorem countScalarFiberLinear_extra_generator (hc : ∀ j ∈ J, c j ≤ c' j)
    (a : PositiveScalars (K := K) m d J c) (p : Space m d q J c' O)
    (j : J) (i : Fin (c' j.val)) (hi : c j.val ≤ i.val) :
    generator (countScalarFiberLinear hc (a,p)) (Sum.inr ⟨j,i⟩)=
      generator p (Sum.inr ⟨j,i⟩) := by
  change rename Sum.inr ((countScalarFiberLinear hc (a,p)).1 (Sum.inr ⟨j,i⟩)).val +
    (p.2 j i).val = rename Sum.inr (p.1 (Sum.inr ⟨j,i⟩)).val + (p.2 j i).val
  rw [countScalarFiberLinear_extra hc a p j i hi]

theorem countScalarFiberLinear_restrict (hc : ∀ j ∈ J, c j ≤ c' j)
    (a : PositiveScalars (K := K) m d J c) (p : Space m d q J c' O) :
    restrictCounts hc (countScalarFiberLinear hc (a,p))=
      scalarFiberCoordinates.symm (a,(scalarFiberCoordinates (restrictCounts hc p)).2) := by
  apply Prod.ext
  · funext i
    cases i with
    | inl i => rfl
    | inr i => exact countScalarFiberLinear_old hc a p i
  · rfl

theorem countScalarFiberLinear_at (hc : ∀ j ∈ J, c j ≤ c' j)
    (p : Space m d q J c' O) :
    countScalarFiberLinear hc ((scalarFiberCoordinates (restrictCounts hc p)).1,p)=p := by
  apply Prod.ext
  · funext i
    cases i with
    | inl i => rfl
    | inr a =>
      rcases a with ⟨j,i⟩
      by_cases hi : i.val < c j.val
      · simp only [countScalarFiberLinear,LinearMap.coe_mk,AddHom.coe_mk,
          Sum.elim_inr,dite_eq_left hi]
        change (restrictCounts hc p).1 (Sum.inr
          ((Fintype.equivFin (ProductRows.LayerLabel J c)).symm
            ((Fintype.equivFin (ProductRows.LayerLabel J c)) ⟨j,⟨i.val,hi⟩⟩))) = _
        rw [Equiv.symm_apply_apply]
        rfl
      · simp [countScalarFiberLinear,hi]
  · rfl

def fullCountScalarFiberLinear (hc : ∀ j ∈ J, c j ≤ c' j) :
    PositiveScalars (K := K) m d J c ×
      FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J c' O →ₗ[K]
        FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J c' O where
  toFun x := (x.2.1,(countScalarFiberLinear hc (x.1,x.2.2.1),x.2.2.2))
  map_add' x y := by
    apply Prod.ext
    · rfl
    apply Prod.ext
    · exact (countScalarFiberLinear hc).map_add (x.1,x.2.2.1) (y.1,y.2.2.1)
    · rfl
  map_smul' t x := by
    apply Prod.ext
    · rfl
    apply Prod.ext
    · exact (countScalarFiberLinear hc).map_smul t (x.1,x.2.2.1)
    · rfl

theorem fullCountScalarFiberLinear_restrict (hc : ∀ j ∈ J, c j ≤ c' j)
    (a : PositiveScalars (K := K) m d J c)
    (p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J c' O) :
    fullRestrictCounts hc (fullCountScalarFiberLinear hc (a,p))=
      fullScalarFiberCoordinates.symm (a,(fullScalarFiberCoordinates (fullRestrictCounts hc p)).2) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · exact countScalarFiberLinear_restrict hc a p.2.1
  · rfl

theorem fullCountScalarFiberLinear_at (hc : ∀ j ∈ J, c j ≤ c' j)
    (p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J c' O) :
    fullCountScalarFiberLinear hc ((fullScalarFiberCoordinates (fullRestrictCounts hc p)).1,p)=p := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · exact countScalarFiberLinear_at hc p.2.1
  · rfl

theorem principal_open_full_count_scalar_fiber_at (hc : ∀ j ∈ J, c j ≤ c' j)
    (hO : ∀ j ∈ J, O j ≤ Forms K h j) :
    letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J c' O) :=
      FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
    ∀ (D : MvPolynomial (Fin (finrank K
      (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J c' O))) K)
      (p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J c' O),
      eval ((Module.finBasis K _).equivFun p) D ≠ 0 →
      ∃ A : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) m d J c))) K,
        eval ((Module.finBasis K _).equivFun
          (fullScalarFiberCoordinates (fullRestrictCounts hc p)).1) A ≠ 0 ∧
        ∀ a, eval ((Module.finBasis K _).equivFun a) A ≠ 0 →
          eval ((Module.finBasis K _).equivFun (fullCountScalarFiberLinear hc (a,p))) D ≠ 0 := by
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J c' O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  intro D p hp
  apply principal_open_freeze_at (fullCountScalarFiberLinear hc)
    (fullScalarFiberCoordinates (fullRestrictCounts hc p)).1 p D
  simpa only [fullCountScalarFiberLinear_at] using hp

end Froberg.PreparedParameters
