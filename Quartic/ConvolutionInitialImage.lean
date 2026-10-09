module

public import Quartic.FreeCoefficientProducts
public import Quartic.OrderedFreeExponents
public import Quartic.WeightedInitialImage

@[expose] public section

/-!
# Initial free-coefficient subspaces for actual quotient multiplication

The finite filtration comparison is applied to the literal free-coefficient
expansion of the convolution quotient. Its graded support condition is proved
from multiplication of inserted polynomial representatives.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Quartic.ConvolutionInitialImage
open MvPolynomial FreeCoefficients ConvolutionFreePieces ConvolutionFreeMultiplication
open ConvolutionLayers FreeCoefficientProducts OrderedFreeExponents
open WeightedInitialImage
variable {K : Type*} [Field K] {t w d : ℕ}

/-- Actual core quotient blocks in increasing free-monomial order. -/
abbrev CoreBlock (K : Type*) [Field K] (t w d : ℕ)
    (i : Fin (Fintype.card (BoundedExponent w d))) :=
  Piece K t 0 (d - (enumerate w d i).val.degree)

/-- The canonical coefficient decomposition, with increasingly ordered indices. -/
def orderedPiecesEquiv : Piece K t w d ≃ₗ[K]
    ((i : Fin (Fintype.card (BoundedExponent w d))) → CoreBlock K t w d i) :=
  quotientPiecesEquiv.trans
    (LinearEquiv.piCongrLeft' K _ (enumerate w d).symm)

@[simp] theorem orderedPiecesEquiv_apply (x : Piece K t w d)
    (i : Fin (Fintype.card (BoundedExponent w d))) :
    orderedPiecesEquiv x i = quotientPiecesEquiv x (enumerate w d i) := rfl

/-- Insert a bounded free monomial, using its complementary core degree. -/
def boundedInsert (b : BoundedExponent w d) :
    Piece K t 0 (d - b.val.degree) →ₗ[K] Piece K t w d :=
  (pieceCast (Nat.sub_add_cancel b.property)).toLinearMap.comp (pieceLift b.val)

@[simp] theorem boundedInsert_mk (b : BoundedExponent w d)
    (v : ConvolutionFree.Target K t 0 (d - b.val.degree)) :
    boundedInsert b (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (targetCast (Nat.sub_add_cancel b.property) (rowLift b.val v)) := by
  simp [boundedInsert]

/-- Inserting a core class gives exactly one nonzero free-coefficient block. -/
theorem quotientPiecesEquiv_boundedInsert (b : BoundedExponent w d)
    (x : Piece K t 0 (d - b.val.degree)) :
    quotientPiecesEquiv (boundedInsert b x) = Pi.single b x := by
  classical
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  funext e
  rw [boundedInsert_mk, quotientPiecesEquiv_mk]
  by_cases he : e = b
  · subst e
    rw [Pi.single_eq_same]
    apply congrArg (relations K t 0 (d - b.val.degree)).mkQ
    funext r
    apply Subtype.ext
    change freeCoeff b.val (targetCast _ (rowLift b.val v) r).val = (v r).val
    simp [freeCoeff_liftCoeff]
  · rw [Pi.single_eq_of_ne he]
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk 0
    apply congrArg (relations K t 0 (d - e.val.degree)).mkQ
    funext r
    apply Subtype.ext
    change freeCoeff e.val (targetCast _ (rowLift b.val v) r).val = 0
    have hbe : b.val ≠ e.val := fun h => he (Subtype.ext h.symm)
    simp [freeCoeff_liftCoeff, hbe]

/-- The inverse coefficient decomposition inserts a single core class literally. -/
theorem quotientPiecesEquiv_symm_single (b : BoundedExponent w d)
    (x : Piece K t 0 (d - b.val.degree)) :
    quotientPiecesEquiv.symm (Pi.single b x) = boundedInsert b x := by
  apply quotientPiecesEquiv.injective
  rw [LinearEquiv.apply_symm_apply, quotientPiecesEquiv_boundedInsert]

/-- The sorted inverse decomposition also inserts its selected free monomial. -/
theorem orderedPiecesEquiv_symm_single
    (i : Fin (Fintype.card (BoundedExponent w d))) (x : CoreBlock K t w d i) :
    orderedPiecesEquiv.symm (Pi.single i x) = boundedInsert (enumerate w d i) x := by
  classical
  apply orderedPiecesEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  funext j
  rw [orderedPiecesEquiv_apply, quotientPiecesEquiv_boundedInsert]
  by_cases h : j = i
  · subst j
    simp
  · have h' : enumerate w d j ≠ enumerate w d i := (enumerate w d).injective.ne h
    simp [h, h']

/-- A single multiplier block reconstructs its actual inserted homogeneous polynomial. -/
theorem homogeneousPiecesEquiv_symm_single (b : BoundedExponent w d)
    (f : Quartic.Forms K t (d - b.val.degree)) :
    homogeneousPiecesEquiv.symm (Pi.single b f) = homogeneousLift b f := by
  classical
  apply homogeneousPiecesEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  funext e
  by_cases he : e = b
  · subst e
    apply Subtype.ext
    simp [homogeneousPiecesEquiv, freeCoeff_liftCoeff]
  · rw [Pi.single_eq_of_ne he]
    apply Subtype.ext
    change 0 = freeCoeff e.val (homogeneousLift b f).val
    have hbe : b.val ≠ e.val := fun h => he (Subtype.ext h.symm)
    simp [freeCoeff_liftCoeff, hbe]

/-- Multiplication is linear in the actual homogeneous multiplier as well. -/
def pieceBilinear {k : ℕ} : Quartic.Forms K (t + w) k →ₗ[K]
    Piece K t w d →ₗ[K] Piece K t w (d + k) where
  toFun := pieceMul
  map_add' f g := by
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on _ x ?_
    intro v
    simp only [pieceMul_mk, LinearMap.add_apply, ← Submodule.Quotient.mk_add]
    apply congrArg (relations K t w (d + k)).mkQ
    funext r
    apply Subtype.ext
    exact add_mul f.val g.val (v r).val
  map_smul' a f := by
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on _ x ?_
    intro v
    simp only [pieceMul_mk, LinearMap.smul_apply, ← Submodule.Quotient.mk_smul]
    apply congrArg (relations K t w (d + k)).mkQ
    funext r
    apply Subtype.ext
    exact smul_mul_assoc a f.val (v r).val

/-- Actual quadratic multiplication, expressed in the ordered coefficient blocks. -/
def coordinateMul : Pieces K t w 2 →ₗ[K]
    ((i : Fin (Fintype.card (BoundedExponent w 1))) → CoreBlock K t w 1 i) →ₗ[K]
    ((i : Fin (Fintype.card (BoundedExponent w 3))) → CoreBlock K t w 3 i) where
  toFun a := orderedPiecesEquiv.toLinearMap.comp
    ((pieceBilinear (homogeneousPiecesEquiv.symm a)).comp orderedPiecesEquiv.symm.toLinearMap)
  map_add' a b := by ext x; simp
  map_smul' a b := by ext x; simp

@[simp] theorem coordinateMul_apply (a : Pieces K t w 2)
    (x : (i : Fin (Fintype.card (BoundedExponent w 1))) → CoreBlock K t w 1 i) :
    coordinateMul a x = orderedPiecesEquiv
      (pieceMul (homogeneousPiecesEquiv.symm a) (orderedPiecesEquiv.symm x)) := rfl

set_option backward.isDefEq.respectTransparency true in
/-- A product of inserted multiplier and source blocks has only the summed free exponent. -/
theorem inserted_product_support (b : BoundedExponent w 2) (c : BoundedExponent w 1)
    (f : Quartic.Forms K t (2 - b.val.degree)) (x : Piece K t 0 (1 - c.val.degree))
    (e : BoundedExponent w 3) (he : e.val ≠ b.val + c.val) :
    quotientPiecesEquiv (pieceMul (homogeneousLift b f) (boundedInsert c x)) e = 0 := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  rw [boundedInsert_mk, pieceMul_mk, quotientPiecesEquiv_mk]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk 0
  apply congrArg (relations K t 0 (3 - e.val.degree)).mkQ
  funext r
  apply Subtype.ext
  change freeCoeff e.val ((homogeneousLift b f).val *
    (targetCast _ (rowLift c.val v) r).val) = 0
  simp only [homogeneousLift_apply_val, targetCast_apply_val, rowLift_apply_val]
  rw [freeCoeff_lift_product, ite_eq_right he.symm]

/-- The required graded-support hypothesis follows from actual polynomial multiplication. -/
theorem coordinateMul_support (b : BoundedExponent w 2)
    (j : Fin (Fintype.card (BoundedExponent w 1)))
    (f : Quartic.Forms K t (2 - b.val.degree)) (x : CoreBlock K t w 1 j)
    (k : Fin (Fintype.card (BoundedExponent w 3))) (hk : k ≠ quadraticShift b j) :
    coordinateMul (Pi.single b f) (Pi.single j x) k = 0 := by
  classical
  rw [coordinateMul_apply, homogeneousPiecesEquiv_symm_single,
    orderedPiecesEquiv_symm_single, orderedPiecesEquiv_apply]
  apply inserted_product_support
  intro h
  apply hk
  apply (enumerate w 3).injective
  apply Subtype.ext
  rw [enumerate_quadraticShift_val]
  exact h

/-- Multiplication of an arbitrary actual degree-one subspace by all quadrics. -/
def quadraticImage (L : Submodule K (Piece K t w 1)) : Submodule K (Piece K t w 3) :=
  ⨆ f : Quartic.Forms K (t + w) 2, L.map (pieceMul f)

/-- The same actual multiplication image in ordered free-coefficient coordinates. -/
theorem map_quadraticImage (L : Submodule K (Piece K t w 1)) :
    (quadraticImage L).map orderedPiecesEquiv.toLinearMap =
      multiplicationImage (K := K) (E := CoreBlock K t w 1) (T := CoreBlock K t w 3)
        (coordinateMul (K := K) (t := t) (w := w))
        (L.map (orderedPiecesEquiv (K := K) (t := t) (w := w) (d := 1)).toLinearMap) := by
  classical
  rw [quadraticImage, Submodule.map_iSup, multiplicationImage]
  apply le_antisymm
  · apply iSup_le
    intro f
    apply le_trans _ (le_iSup _ (homogeneousPiecesEquiv f))
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    apply le_of_eq
    congr 1
    apply LinearMap.ext
    intro x
    simp
  · apply iSup_le
    intro a
    apply le_trans _ (le_iSup _ (homogeneousPiecesEquiv.symm a))
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    apply le_of_eq
    congr 1
    apply LinearMap.ext
    intro x
    simp

/-- Independent initial subspaces of the individual core coefficient blocks. -/
def initialCoefficients (L : Submodule K (Piece K t w 1))
    (i : Fin (Fintype.card (BoundedExponent w 1))) : Submodule K (CoreBlock K t w 1 i) :=
  FilteredImage.initialPiece (CoreBlock K t w 1)
    (L.map orderedPiecesEquiv.toLinearMap) i

/-- The actual subspace corresponding to all independent initial coefficients. -/
def initial (L : Submodule K (Piece K t w 1)) : Submodule K (Piece K t w 1) :=
  (initialSubspace (CoreBlock K t w 1) (L.map orderedPiecesEquiv.toLinearMap)).map
    orderedPiecesEquiv.symm.toLinearMap

/-- The initial replacement has completely independent free-coefficient components. -/
theorem map_initial (L : Submodule K (Piece K t w 1)) :
    (initial L).map orderedPiecesEquiv.toLinearMap =
      Submodule.pi Set.univ (initialCoefficients (K := K) (t := t) (w := w) L) := by
  rw [initial, ← Submodule.map_comp]
  simp only [LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
    LinearEquiv.refl_toLinearMap, Submodule.map_id]
  rfl

/-- Actual free-coefficient degeneration preserves the complete source dimension. -/
theorem initial_finrank (L : Submodule K (Piece K t w 1)) :
    Module.finrank K (initial L) = Module.finrank K L := by
  rw [initial, orderedPiecesEquiv.symm.finrank_map_eq,
    initialSubspace_finrank, orderedPiecesEquiv.finrank_map_eq]

/-- The independent coefficient dimensions sum to the original subspace dimension. -/
theorem sum_initialCoefficients_finrank (L : Submodule K (Piece K t w 1)) :
    ∑ i, Module.finrank K (initialCoefficients L i) = Module.finrank K L := by
  rw [← orderedPiecesEquiv.finrank_map_eq L]
  exact FilteredImage.sum_initialPiece_finrank _ _

/-- Passing to independent initial coefficients cannot increase the actual quadratic image. -/
theorem quadraticImage_initial_finrank_le (L : Submodule K (Piece K t w 1)) :
    Module.finrank K (quadraticImage (initial L)) ≤ Module.finrank K (quadraticImage L) := by
  classical
  have h := multiplicationImage_initial_finrank_le (K := K)
    (E := CoreBlock K t w 1) (T := CoreBlock K t w 3)
    (coordinateMul (K := K) (t := t) (w := w))
    quadraticShift quadraticShift_strictMono coordinateMul_support
    (L.map orderedPiecesEquiv.toLinearMap)
  rw [← map_quadraticImage, orderedPiecesEquiv.finrank_map_eq] at h
  have hinit : Submodule.pi Set.univ (initialCoefficients (K := K) (t := t) (w := w) L) =
      initialSubspace (CoreBlock K t w 1) (L.map orderedPiecesEquiv.toLinearMap) := rfl
  rw [← hinit, ← map_initial, ← map_quadraticImage,
    orderedPiecesEquiv.finrank_map_eq] at h
  exact h

/-- Every actual degree-one subspace has the required independent initial replacement. -/
theorem exists_initial_replacement (L : Submodule K (Piece K t w 1)) :
    ∃ L₀ : Submodule K (Piece K t w 1),
      Module.finrank K L₀ = Module.finrank K L ∧
      Module.finrank K (quadraticImage L₀) ≤ Module.finrank K (quadraticImage L) ∧
      ∃ C : (i : Fin (Fintype.card (BoundedExponent w 1))) → Submodule K (CoreBlock K t w 1 i),
        L₀.map orderedPiecesEquiv.toLinearMap = Submodule.pi Set.univ C :=
  ⟨initial L, initial_finrank L, quadraticImage_initial_finrank_le L,
    initialCoefficients L, map_initial L⟩

end Quartic.ConvolutionInitialImage
