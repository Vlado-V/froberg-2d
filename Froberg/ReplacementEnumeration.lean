import Froberg.OddBackgroundProductCompatibility
import Froberg.TupleReplacement

/-! The biform even-slot pencil is exactly a single-slot replacement of
the enumerated homogeneous generator tuple. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}

def backgroundEvenIndex (i : Fin q) : Fin (Fintype.card (BackgroundLabel q f u)) :=
  (Fintype.equivFin (BackgroundLabel q f u)) (Sum.inl i)

theorem backgroundEnumeratedForms_even
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1) (i : Fin q) :
    backgroundEnumeratedForms Q F G (backgroundEvenIndex i)=evenPolynomialToForms (Q i) := by
  apply Subtype.ext
  change rename finSumFinEquiv
    (backgroundParityFamily Q F G ((Fintype.equivFin _).symm ((Fintype.equivFin _) (Sum.inl i)))).val=
      rename finSumFinEquiv (Q i).val
  rw [Equiv.symm_apply_apply]
  rfl

theorem backgroundEnumeratedForms_update
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (i : Fin q) (M : biformParitySpace K h m d 0) :
    backgroundEnumeratedForms (Function.update Q i M) F G=
      Function.update (backgroundEnumeratedForms Q F G) (backgroundEvenIndex i)
        (evenPolynomialToForms M) := by
  classical
  funext k
  obtain ⟨j,rfl⟩ := (Fintype.equivFin (BackgroundLabel q f u)).surjective k
  rcases j with j | (j | j)
  · by_cases hj : j=i
    · subst j
      rw [←backgroundEvenIndex,Function.update_self,backgroundEnumeratedForms_even,Function.update_self]
    · have hij : (Fintype.equivFin (BackgroundLabel q f u)) (Sum.inl j)≠backgroundEvenIndex (f := f) (u := u) i := by
        intro he
        exact hj (Sum.inl.inj ((Fintype.equivFin (BackgroundLabel q f u)).injective he))
      rw [Function.update_of_ne hij]
      change backgroundEnumeratedForms (Function.update Q i M) F G (backgroundEvenIndex j)=_
      rw [backgroundEnumeratedForms_even,Function.update_of_ne hj]
      exact (backgroundEnumeratedForms_even Q F G j).symm
  · have hij : (Fintype.equivFin (BackgroundLabel q f u)) (Sum.inr (Sum.inl j))≠backgroundEvenIndex (f := f) (u := u) i := by
      intro he
      have hh := (Fintype.equivFin (BackgroundLabel q f u)).injective he
      cases hh
    rw [Function.update_of_ne hij]
    apply Subtype.ext
    change rename finSumFinEquiv
      (backgroundParityFamily (Function.update Q i M) F G
        ((Fintype.equivFin _).symm ((Fintype.equivFin _) (Sum.inr (Sum.inl j))))).val=
      rename finSumFinEquiv (backgroundParityFamily Q F G
        ((Fintype.equivFin _).symm ((Fintype.equivFin _) (Sum.inr (Sum.inl j))))).val
    rw [Equiv.symm_apply_apply]
    rfl
  · have hij : (Fintype.equivFin (BackgroundLabel q f u)) (Sum.inr (Sum.inr j))≠backgroundEvenIndex (f := f) (u := u) i := by
      intro he
      have hh := (Fintype.equivFin (BackgroundLabel q f u)).injective he
      cases hh
    rw [Function.update_of_ne hij]
    apply Subtype.ext
    change rename finSumFinEquiv
      (backgroundParityFamily (Function.update Q i M) F G
        ((Fintype.equivFin _).symm ((Fintype.equivFin _) (Sum.inr (Sum.inr j))))).val=
      rename finSumFinEquiv (backgroundParityFamily Q F G
        ((Fintype.equivFin _).symm ((Fintype.equivFin _) (Sum.inr (Sum.inr j))))).val
    rw [Equiv.symm_apply_apply]
    rfl

theorem backgroundEnumeratedForms_slot_pencil
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (i : Fin q) (M : biformParitySpace K h m d 0) (c : K) :
    backgroundEnumeratedForms (Function.update Q i (Q i+c • M)) F G=
      Function.update (backgroundEnumeratedForms Q F G) (backgroundEvenIndex i)
        (backgroundEnumeratedForms Q F G (backgroundEvenIndex i)+c • evenPolynomialToForms M) := by
  rw [backgroundEnumeratedForms_update,backgroundEnumeratedForms_even,map_add,map_smul]

end Froberg
