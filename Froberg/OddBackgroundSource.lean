module

public import Froberg.OddBackgroundEndpoint
public import Froberg.ParitySourceQuotient

@[expose] public section

/-! The actual odd coefficient space has precisely the constant F and U+P
relations. Even scalar generators disappear under the parity projection. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}

def backgroundOddFamily (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1) :
    BackgroundLabel q f u → biformParitySpace K h m d 1 :=
  Sum.elim (fun _ => 0) (Sum.elim F G)

theorem backgroundOddFamily_span (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1) :
    Submodule.span K (Set.range (backgroundOddFamily (q := q) F G))=
      Submodule.span K (Set.range F) ⊔ Submodule.span K (Set.range G) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    rcases i with i | (i | i)
    · exact Submodule.zero_mem _
    · exact (show Submodule.span K (Set.range F)≤_ from le_sup_left)
        (Submodule.subset_span ⟨i,rfl⟩)
    · exact (show Submodule.span K (Set.range G)≤_ from le_sup_right)
        (Submodule.subset_span ⟨i,rfl⟩)
  · apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Submodule.subset_span ⟨Sum.inr (Sum.inl i),rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Submodule.subset_span ⟨Sum.inr (Sum.inr i),rfl⟩

theorem background_parity_projection
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (i : BackgroundLabel q f u) :
    parityProjectionToPart
      ((fun j => (blockWeight h m j : ZMod 2)) ∘ finSumFinEquiv.symm) 1
      (parityPolynomialToFormsEquiv finSumFinEquiv
        (fun j => (blockWeight h m j : ZMod 2)) (backgroundParity i)
        (backgroundParityFamily Q F G i)).val=
    parityPolynomialToFormsEquiv finSumFinEquiv (fun j => (blockWeight h m j : ZMod 2)) 1
      (backgroundOddFamily F G i) := by
  rcases i with i | (i | i)
  · apply Subtype.ext
    change parityForm _ 1 (parityPolynomialToFormsEquiv _ _ 0 (Q i)).val=
      (parityPolynomialToFormsEquiv _ _ 1 (0 : biformParitySpace K h m d 1)).val
    rw [(parityPolynomialToFormsEquiv (K := K) (d := d) finSumFinEquiv
      (fun j => (blockWeight h m j : ZMod 2)) 1).map_zero]
    exact parityForm_other _ 1 0 _ (parityPolynomialToFormsEquiv _ _ 0 (Q i)).property one_ne_zero
  · apply Subtype.ext
    exact parityForm_same _ 1 _ (parityPolynomialToFormsEquiv _ _ 1 (F i)).property
  · apply Subtype.ext
    exact parityForm_same _ 1 _ (parityPolynomialToFormsEquiv _ _ 1 (G i)).property

theorem background_source_relations_map
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :
    (Submodule.span K (Set.range F) ⊔ Submodule.span K (Set.range G)).map
      (parityPolynomialToFormsEquiv finSumFinEquiv (fun i => (blockWeight h m i : ZMod 2)) 1).toLinearMap=
    Submodule.span K (Set.range (fun i => parityProjectionToPart
      ((fun j => (blockWeight h m j : ZMod 2)) ∘ finSumFinEquiv.symm) 1
      (backgroundEnumeratedForms Q F G i))) := by
  rw [←backgroundOddFamily_span (q := q),Submodule.map_span,←Set.range_comp']
  congr 1
  ext z
  constructor
  · rintro ⟨i,rfl⟩
    refine ⟨(Fintype.equivFin (BackgroundLabel q f u)) i,?_⟩
    change parityProjectionToPart _ 1
      (parityPolynomialToFormsEquiv _ _ _
        (backgroundParityFamily Q F G ((Fintype.equivFin _).symm ((Fintype.equivFin _) i)))).val=_
    rw [Equiv.symm_apply_apply]
    exact background_parity_projection Q F G i
  · rintro ⟨i,rfl⟩
    exact ⟨(Fintype.equivFin (BackgroundLabel q f u)).symm i,
      (background_parity_projection Q F G _).symm⟩

def oddBackgroundSourceEquiv (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :
    (biformParitySpace K h m d 1 ⧸
      (Submodule.span K (Set.range F) ⊔ Submodule.span K (Set.range G))) ≃ₗ[K]
      oddCoefficientSpace ((fun j => (blockWeight h m j : ZMod 2)) ∘ finSumFinEquiv.symm)
        (backgroundEnumeratedForms Q F G) :=
  (Submodule.Quotient.equiv _ _
    (parityPolynomialToFormsEquiv finSumFinEquiv (fun i => (blockWeight h m i : ZMod 2)) 1)
    (background_source_relations_map Q F G)).trans
    (oddSourceQuotientEquiv _ (backgroundParity ∘ (Fintype.equivFin (BackgroundLabel q f u)).symm)
      (backgroundEnumeratedForms Q F G)
      (parityEnumeratedForms_homogeneous _ _ _ _ _))

end Froberg
