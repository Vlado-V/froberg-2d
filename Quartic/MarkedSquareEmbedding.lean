module

public import Quartic.AugmentedMiddle

@[expose] public section

/-!
# An independent marked square in the child variables

The first `c` variables support the mixed-family products. The square of the
next variable gives one more independent quadratic coordinate, over every field.
-/

noncomputable section
namespace Quartic.MarkedSquareEmbedding
open Module MvPolynomial AugmentedMiddle

variable {K : Type*} [Field K] {m c : ℕ}

/-- The first child variable outside the active `c` variables. -/
def extraVariable (hc : c < m) : Forms K m 1 :=
  ⟨X ⟨c, hc⟩, isHomogeneous_X K _⟩

/-- Its square is independent of all active quadratic forms. -/
def extraSquare (hc : c < m) : Forms K m 2 :=
  ⟨X ⟨c, hc⟩ ^ 2, by
    simpa using (isHomogeneous_X K (⟨c, hc⟩ : Fin m)).pow 2⟩

/-- The active products together with the marked-square coordinate. -/
def embedding (hc : c < m) : (Forms K c 2 × K) →ₗ[K] Forms K m 2 :=
  (activeForms hc.le 2).coprod (LinearMap.toSpanSingleton K _ (extraSquare hc))

@[simp] theorem embedding_apply (hc : c < m) (b : Forms K c 2) (a : K) :
    embedding hc (b, a) = activeForms hc.le 2 b + a • extraSquare hc := rfl

theorem extraIndex_not_active (hc : c < m) :
    (⟨c, hc⟩ : Fin m) ∉ Set.range (Fin.castLE hc.le) := by
  rintro ⟨i, hi⟩
  have he := congrArg Fin.val hi
  exact (Nat.ne_of_lt i.isLt) he

/-- Reading the marked-square coefficient kills every active quadratic form. -/
theorem activeForms_extraSquare_coefficient (hc : c < m) (b : Forms K c 2) :
    (activeForms hc.le 2 b).val.coeff (Finsupp.single (⟨c, hc⟩ : Fin m) 2) = 0 := by
  classical
  apply coeff_rename_eq_zero
  intro u hu
  have hz := Finsupp.mapDomain_of_notMem_range u (⟨c, hc⟩ : Fin m)
    (extraIndex_not_active hc)
  rw [hu, Finsupp.single_eq_same] at hz
  exact (by omega : False).elim

@[simp] theorem extraSquare_coefficient (hc : c < m) :
    (extraSquare (K := K) hc).val.coeff (Finsupp.single (⟨c, hc⟩ : Fin m) 2) = 1 := by
  classical
  simp [extraSquare, coeff_X_pow]

/-- No characteristic restriction is needed for the marked-square embedding. -/
theorem embedding_injective (hc : c < m) :
    Function.Injective (embedding (K := K) hc) := by
  rintro ⟨b, a⟩ ⟨b', a'⟩ h
  have ha := congrArg (fun p : Forms K m 2 =>
    p.val.coeff (Finsupp.single (⟨c, hc⟩ : Fin m) 2)) h
  have haa : a = a' := by
    simpa only [embedding_apply, Submodule.coe_add, Submodule.coe_smul,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_smul,
      activeForms_extraSquare_coefficient,
      extraSquare_coefficient, smul_eq_mul, mul_one, zero_add] using ha
  apply Prod.ext _ haa
  apply activeForms_injective hc.le 2
  simpa only [embedding_apply, haa, add_left_inj] using h

theorem finrank_source : finrank K (Forms K c 2 × K) = (c + 1).choose 2 + 1 := by
  simp [finrank_quadrics]

/-- A mixed marked generator whose reduced square is the new coordinate. -/
def zeta (hc : c < m) : MiddleCoordinates.Mixed K m :=
  ![extraVariable hc, 0, 0]

theorem zeta_product (hc : c < m) :
    MiddleCoordinates.projectedProduct (zeta (K := K) hc) (zeta hc) =
      (extraSquare hc, 0) := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [MiddleCoordinates.projectedProduct, MiddleCoordinates.mulLinear,
      zeta, extraVariable, extraSquare, pow_two]

/-- The old mixed products occupy precisely the active part of the embedding. -/
theorem mixedFamily_product (hc : c < m) (i j : Fin c) :
    MiddleCoordinates.projectedProduct (AugmentedMiddle.mixedFamily (K := K) hc.le i)
      (AugmentedMiddle.mixedFamily hc.le j) =
      (embedding hc (quadraticMonomial i j, 0), 0) := by
  simpa using AugmentedMiddle.mixedFamily_product (K := K) hc.le i j

end Quartic.MarkedSquareEmbedding
