module

public import Quartic.ConvolutionLayers

@[expose] public section

/-!
# Actual multiplication in free-monomial coordinates

Products add the free exponent vectors and multiply the core polynomials.
The identity is proved first in the polynomial ring, then on the actual
quotient pieces, including all homogeneous-degree transports.
-/

noncomputable section
namespace Quartic.FreeCoefficientProducts
open MvPolynomial FreeCoefficients FreeMonomialCounts
open ConvolutionFreePieces ConvolutionFreeMultiplication ConvolutionLayers
variable {K : Type*} [Field K] {t w d k : ℕ}

theorem mergeExponent_add (a a' : Fin t →₀ ℕ) (b b' : Fin w →₀ ℕ) :
    mergeExponent (a + a') (b + b') = mergeExponent a b + mergeExponent a' b' := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp

/-- Polynomial multiplication adds the free monomial exponents exactly. -/
theorem liftCoeff_mul (b c : Fin w →₀ ℕ) (p q : Quartic.Poly K t) :
    liftCoeff b p * liftCoeff c q = liftCoeff (b + c) (p * q) := by
  rw [liftCoeff_eq_mul, liftCoeff_eq_mul, liftCoeff_eq_mul, map_mul]
  have hm : monomial (mergeExponent (0 : Fin t →₀ ℕ) b) (1 : K) *
      monomial (mergeExponent (0 : Fin t →₀ ℕ) c) 1 =
        monomial (mergeExponent (0 : Fin t →₀ ℕ) (b + c)) 1 := by
    rw [monomial_mul_monomial, one_mul, ← mergeExponent_add]
    simp
  rw [← hm]
  ring

/-- Coefficients of a product supported at two free monomials. -/
theorem freeCoeff_lift_product (b c e : Fin w →₀ ℕ) (p q : Quartic.Poly K t) :
    freeCoeff e (liftCoeff b p * liftCoeff c q) =
      if b + c = e then p * q else 0 := by
  rw [liftCoeff_mul, freeCoeff_liftCoeff]

/-- Insert a free monomial into a homogeneous multiplier. -/
def formLift (b : Fin w →₀ ℕ) :
    Quartic.Forms K t k →ₗ[K] Quartic.Forms K (t + w) (k + b.degree) :=
  ((liftCoeff b).comp (Quartic.Forms K t k).subtype).codRestrict _
    (fun p => liftCoeff_homogeneous b p.val p.property)

@[simp] theorem formLift_val (b : Fin w →₀ ℕ) (f : Quartic.Forms K t k) :
    (formLift b f).val = liftCoeff b f.val := rfl

theorem productDegree (d k : ℕ) (b c : Fin w →₀ ℕ) :
    (d + k) + (b + c).degree = (d + c.degree) + (k + b.degree) := by
  rw [map_add]
  omega

/-- The row-level graded multiplication identity on the actual presentation. -/
theorem rowLift_product (b c : Fin w →₀ ℕ) (f : Quartic.Forms K t k)
    (v : ConvolutionFree.Target K t 0 d) :
    rowMul (formLift b f) (rowLift c v) =
      targetCast (productDegree d k b c) (rowLift (b + c) (rowMul (w := 0) f v)) := by
  funext r
  apply Subtype.ext
  simp only [rowMul_apply_val, rowLift_apply_val, targetCast_apply_val, formLift_val,
    liftCoeff_mul]

/-- On actual quotient classes, products add the free monomials and multiply the core class. -/
theorem pieceLift_product (b c : Fin w →₀ ℕ) (f : Quartic.Forms K t k) (x : Piece K t 0 d) :
    pieceMul (formLift b f) (pieceLift c x) =
      pieceCast (productDegree d k b c) (pieceLift (b + c) (pieceMul (w := 0) f x)) := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  simp only [pieceLift_mk, pieceMul_mk, pieceCast_mk]
  exact congrArg (relations K t w ((d + c.degree) + (k + b.degree))).mkQ
    (rowLift_product b c f v)

/-- Insert at a free monomial whose degree is supplied in its type. -/
def insertAt (b : ExactExponent w k) : Piece K t 0 d →ₗ[K] Piece K t w (d + k) :=
  (pieceCast (congrArg (d + ·) b.property)).toLinearMap.comp (pieceLift b.val)

theorem insertAt_injective (b : ExactExponent w k) :
    Function.Injective (insertAt (K := K) (t := t) (d := d) b) :=
  (pieceCast _).injective.comp (pieceLift_injective b.val)

@[simp] theorem insertAt_mk (b : ExactExponent w k) (v : ConvolutionFree.Target K t 0 d) :
    insertAt b (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (targetCast (congrArg (d + ·) b.property) (rowLift b.val v)) := by
  simp [insertAt]

/-- Add exact free exponents, retaining their degree in the type. -/
def addExponent {u v : ℕ} (b : ExactExponent w u) (c : ExactExponent w v) :
    ExactExponent w (u + v) := ⟨b.val + c.val, by simp [b.property, c.property]⟩

@[simp] theorem addExponent_zero (b : ExactExponent w k) :
    addExponent b (zeroExponent w) = b := by
  apply Subtype.ext
  simp [addExponent, zeroExponent]

/-- Insert an exact-degree free monomial into a homogeneous multiplier. -/
def formAt {u : ℕ} (b : ExactExponent w u) (f : Quartic.Forms K t k) :
    Quartic.Forms K (t + w) (k + u) :=
  ⟨liftCoeff b.val f.val, by
    change (liftCoeff b.val f.val).IsHomogeneous (k + u)
    simpa only [b.property] using liftCoeff_homogeneous b.val f.val f.property⟩

theorem exactProductDegree (d k u v : ℕ) : (d + k) + (u + v) = (d + v) + (k + u) := by omega

/-- The multiplication identity with all free degrees recorded explicitly. -/
theorem insertAt_product {u v : ℕ} (b : ExactExponent w u) (c : ExactExponent w v)
    (f : Quartic.Forms K t k) (x : Piece K t 0 d) :
    pieceMul (formAt b f) (insertAt c x) =
      pieceCast (exactProductDegree d k u v)
        (insertAt (addExponent b c) (pieceMul (w := 0) f x)) := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro x
  simp only [insertAt_mk, pieceMul_mk, pieceCast_mk]
  apply congrArg (relations K t w ((d + v) + (k + u))).mkQ
  funext r
  apply Subtype.ext
  simp only [rowMul_apply_val, rowLift_apply_val, targetCast_apply_val]
  exact liftCoeff_mul b.val c.val f.val (x r).val

/-- A pure free monomial at its exact homogeneous degree. -/
def freeFormAt (b : ExactExponent w k) : Quartic.Forms K (t + w) k :=
  ⟨monomial (mergeExponent (0 : Fin t →₀ ℕ) b.val) 1,
    isHomogeneous_monomial 1 (by simpa using b.property)⟩

/-- A pure free multiplier adds its exponent to the inserted core class. -/
theorem insertAt_free_product {u v : ℕ} (b : ExactExponent w u) (c : ExactExponent w v)
    (x : Piece K t 0 d) :
    pieceMul (freeFormAt b) (insertAt c x) =
      pieceCast (show d + (u + v) = (d + v) + u from by omega)
        (insertAt (addExponent b c) x) := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro x
  simp only [insertAt_mk, pieceMul_mk, pieceCast_mk]
  apply congrArg (relations K t w ((d + v) + u)).mkQ
  funext r
  apply Subtype.ext
  simp only [rowMul_apply_val, rowLift_apply_val, targetCast_apply_val]
  change monomial (mergeExponent 0 b.val) 1 * liftCoeff c.val (x r).val =
    liftCoeff (b.val + c.val) (x r).val
  have h := liftCoeff_mul b.val c.val (1 : Quartic.Poly K t) (x r).val
  simpa only [liftCoeff_eq_mul, map_one, one_mul] using h

end Quartic.FreeCoefficientProducts
