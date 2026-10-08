import Froberg.OrderedMonomials
import Quartic.WeightedInitialImage

/-! Block-valued initial subspaces of the actual attached outer quotient. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open Module MvPolynomial Quartic.HomogeneousCoefficientCoordinates
open Quartic.WeightedInitialImage
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I] {n s d h : ℕ}
variable (e : I → Fin n →₀ ℕ) (v : I → Fin h → K) (he : ∀ i, (e i).degree = s)

abbrev OrderedFiber (c : ℕ) (i : Fin (Fintype.card (Exponent n (s+c)))) :=
  (Fin h → K) ⧸ relationFiber e v (OrderedMonomials.enumerate n (s+c) i).val

def orderedFiberEquiv (c : ℕ) :
    ((Fin h → Forms K n (s+c)) ⧸ relationSpace (d := c) e v he) ≃ₗ[K]
      ((i : Fin (Fintype.card (Exponent n (s+c)))) → OrderedFiber e v c i) :=
  (quotientFiberEquiv e v he).trans
    (LinearEquiv.piCongrLeft' K _ (OrderedMonomials.enumerate n (s+c)).symm)

@[simp] theorem orderedFiberEquiv_apply (c : ℕ)
    (x : (Fin h → Forms K n (s+c)) ⧸ relationSpace (d := c) e v he)
    (i : Fin (Fintype.card (Exponent n (s+c)))) :
    orderedFiberEquiv e v he c x i =
      quotientFiberEquiv e v he x (OrderedMonomials.enumerate n (s+c) i) := rfl

theorem orderedFiberEquiv_symm_single (c : ℕ)
    (i : Fin (Fintype.card (Exponent n (s+c)))) (x : OrderedFiber e v c i) :
    (orderedFiberEquiv e v he c).symm (Pi.single i x) =
      (quotientFiberEquiv e v he).symm
        (Pi.single (OrderedMonomials.enumerate n (s+c) i) x) := by
  apply (orderedFiberEquiv e v he c).injective
  rw [LinearEquiv.apply_symm_apply]
  funext j
  rw [orderedFiberEquiv_apply,LinearEquiv.apply_symm_apply]
  by_cases hij : j=i
  · subst j; simp
  · have heij : OrderedMonomials.enumerate n (s+c) j ≠
        OrderedMonomials.enumerate n (s+c) i := (OrderedMonomials.enumerate n (s+c)).injective.ne hij
    simp [Pi.single_eq_of_ne hij,Pi.single_eq_of_ne heij]

/-- Actual multiplication in ordered monomial coefficient coordinates. -/
def orderedMultiply : (Exponent n d → K) →ₗ[K]
    ((i : Fin (Fintype.card (Exponent n s))) → OrderedFiber e v 0 i) →ₗ[K]
    ((i : Fin (Fintype.card (Exponent n (s+d)))) → OrderedFiber e v d i) where
  toFun f := (orderedFiberEquiv e v he d).toLinearMap.comp
    ((quotientMultiply e v he (equiv.symm f)).comp (orderedFiberEquiv e v he 0).symm.toLinearMap)
  map_add' f g := by ext x; simp
  map_smul' c f := by ext x; simp

private theorem coefficient_single (b : Exponent n d) (c : K) :
    equiv.symm (Pi.single b c) = c • monomialForm b := by
  apply equiv.injective
  rw [LinearEquiv.apply_symm_apply]
  funext a
  by_cases hab : a=b
  · subst a
    simp [equiv_apply,monomialForm]
  · have hval : b.val ≠ a.val := fun hh => hab (Subtype.ext hh.symm)
    simp [Pi.single_eq_of_ne hab,equiv_apply,monomialForm,coeff_monomial,hval]

/-- The required graded support follows from literal monomial multiplication
and the exact quotient-fiber formula. -/
theorem orderedMultiply_support (b : Exponent n d)
    (i : Fin (Fintype.card (Exponent n s))) (c : K) (x : OrderedFiber e v 0 i)
    (j : Fin (Fintype.card (Exponent n (s+d)))) (hji : j ≠ OrderedMonomials.shift b i) :
    orderedMultiply e v he (Pi.single b c) (Pi.single i x) j = 0 := by
  classical
  change orderedFiberEquiv e v he d
    (quotientMultiply e v he (equiv.symm (Pi.single b c))
      ((orderedFiberEquiv e v he 0).symm (Pi.single i x))) j = 0
  rw [coefficient_single,orderedFiberEquiv_symm_single,orderedFiberEquiv_apply]
  change fiberMultiply e v he (c • monomialForm b)
    (Pi.single (OrderedMonomials.enumerate n s i) x)
    (OrderedMonomials.enumerate n (s+d) j) = 0
  rw [map_smul,LinearMap.smul_apply]
  simp only [Pi.smul_apply]
  rw [fiberMultiply_monomial_single]
  have hneq : OrderedMonomials.enumerate n (s+d) j ≠
      addExponent (OrderedMonomials.enumerate n s i) b := by
    intro hh
    apply hji
    apply (OrderedMonomials.enumerate n (s+d)).injective
    simpa only [OrderedMonomials.enumerate_shift] using hh
  rw [Pi.single_eq_of_ne hneq,smul_zero]

/-- The complete actual multiplication image in the target quotient. -/
def outerImage
    (L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)) :
    Submodule K ((Fin h → Forms K n (s+d)) ⧸ relationSpace (d := d) e v he) :=
  Quartic.BilinearImage.image (quotientMultiply e v he) L

theorem map_outerImage
    (L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)) :
    (outerImage (d := d) e v he L).map (orderedFiberEquiv e v he d).toLinearMap =
      multiplicationImage (orderedMultiply (d := d) e v he)
        (L.map (orderedFiberEquiv e v he 0).toLinearMap) := by
  classical
  rw [outerImage,Quartic.BilinearImage.image,Submodule.map_iSup,multiplicationImage]
  apply le_antisymm
  · apply iSup_le
    intro f
    apply le_trans _ (le_iSup _ (equiv f))
    rw [← Submodule.map_comp,← Submodule.map_comp]
    apply le_of_eq
    congr 1
    ext x
    simp [orderedMultiply]
  · apply iSup_le
    intro f
    apply le_trans _ (le_iSup _ (equiv.symm f))
    rw [← Submodule.map_comp,← Submodule.map_comp]
    apply le_of_eq
    congr 1
    ext x
    simp [orderedMultiply]

def initialFibers
    (L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he))
    (i : Fin (Fintype.card (Exponent n s))) : Submodule K (OrderedFiber e v 0 i) :=
  Quartic.FilteredImage.initialPiece (OrderedFiber e v 0)
    (L.map (orderedFiberEquiv e v he 0).toLinearMap) i

def outerInitial
    (L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)) :
    Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he) :=
  (initialSubspace (OrderedFiber e v 0) (L.map (orderedFiberEquiv e v he 0).toLinearMap)).map
    (orderedFiberEquiv e v he 0).symm.toLinearMap

theorem map_outerInitial
    (L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)) :
    (outerInitial e v he L).map (orderedFiberEquiv e v he 0).toLinearMap =
      Submodule.pi Set.univ (initialFibers e v he L) := by
  rw [outerInitial,← Submodule.map_comp]
  simp only [LinearEquiv.comp_coe,LinearEquiv.symm_trans_self,
    LinearEquiv.refl_toLinearMap,Submodule.map_id]
  rfl

theorem outerInitial_finrank
    (L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)) :
    finrank K (outerInitial e v he L) = finrank K L := by
  exact ((orderedFiberEquiv e v he 0).symm.finrank_map_eq _).trans
    ((initialSubspace_finrank _ _).trans ((orderedFiberEquiv e v he 0).finrank_map_eq L))

theorem sum_initialFibers_finrank
    (L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)) :
    ∑ i, finrank K (initialFibers e v he L i) = finrank K L := by
  exact (Quartic.FilteredImage.sum_initialPiece_finrank _ _).trans
    ((orderedFiberEquiv e v he 0).finrank_map_eq L)

/-- The concrete block initial replacement preserves dimension and cannot
increase the actual multiplication image. -/
theorem outerImage_initial_finrank_le
    (L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)) :
    finrank K (outerImage (d := d) e v he (outerInitial e v he L)) ≤
      finrank K (outerImage (d := d) e v he L) := by
  have hh := multiplicationImage_initial_finrank_le (orderedMultiply (d := d) e v he)
    OrderedMonomials.shift OrderedMonomials.shift_strictMono
    (orderedMultiply_support e v he) (L.map (orderedFiberEquiv e v he 0).toLinearMap)
  rw [← map_outerImage,(orderedFiberEquiv e v he d).finrank_map_eq] at hh
  have hi : Submodule.pi Set.univ (initialFibers e v he L) =
      initialSubspace (OrderedFiber e v 0) (L.map (orderedFiberEquiv e v he 0).toLinearMap) := rfl
  rw [← hi,← map_outerInitial,← map_outerImage,
    (orderedFiberEquiv e v he d).finrank_map_eq] at hh
  exact hh

end Froberg.AttachedMultiplication
