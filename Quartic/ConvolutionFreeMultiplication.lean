module

public import Quartic.ConvolutionFreePieces

@[expose] public section

/-!
# Multiplication and coefficient summands in the actual free extension

All maps below descend from polynomial multiplication and free-monomial
insertion or extraction. In particular every core component embeds as a
split summand of the appropriate homogeneous piece of the free extension.
-/

noncomputable section
namespace Quartic.ConvolutionFreeMultiplication
open MvPolynomial FreeCoefficients ConvolutionPresentation ConvolutionFreePieces
variable {K : Type*} [Field K] {t w d k : ℕ}

/-- Multiplication of homogeneous forms in the full variable set. -/
def formMul (f : Quartic.Forms K (t + w) k) :
    Quartic.Forms K (t + w) d →ₗ[K] Quartic.Forms K (t + w) (d + k) where
  toFun p := ⟨f.val * p.val, by
    change (f.val * p.val).IsHomogeneous (d + k)
    simpa only [Nat.add_comm] using f.property.mul p.property⟩
  map_add' _ _ := Subtype.ext (mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (mul_smul_comm _ _ _)

/-- Multiply every output row by the same homogeneous polynomial. -/
def rowMul (f : Quartic.Forms K (t + w) k) :
    ConvolutionFree.Target K t w d →ₗ[K] ConvolutionFree.Target K t w (d + k) :=
  LinearMap.pi fun r => (formMul f).comp (LinearMap.proj r)

@[simp] theorem rowMul_apply_val (f : Quartic.Forms K (t + w) k)
    (v : ConvolutionFree.Target K t w d) (r : Fin 3) :
    (rowMul f v r).val = f.val * (v r).val := rfl

/-- Multiplication by any homogeneous polynomial respects the actual relations. -/
theorem rowMul_maps_relations (f : Quartic.Forms K (t + w) k) :
    relations K t w d ≤ (relations K t w (d + k)).comap (rowMul f) := by
  rintro v ⟨a, ha⟩
  refine ⟨fun s => f.val * a s, ?_⟩
  funext r
  change (∑ i : Fin t, X (Fin.castAdd w i) * (f.val * a (columnIndex r i))) =
    f.val * (v r).val
  have hr := congrFun ha r
  change polyPresentation a r = (v r).val at hr
  rw [← hr, polyPresentation_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Actual graded multiplication on the free polynomial-extension quotient. -/
def pieceMul (f : Quartic.Forms K (t + w) k) :
    Piece K t w d →ₗ[K] Piece K t w (d + k) :=
  Submodule.mapQ _ _ (rowMul f) (rowMul_maps_relations f)

@[simp] theorem pieceMul_mk (f : Quartic.Forms K (t + w) k)
    (v : ConvolutionFree.Target K t w d) :
    pieceMul f (Submodule.Quotient.mk v) = Submodule.Quotient.mk (rowMul f v) := rfl

/-- Insert a fixed free monomial into all three core output rows. -/
def rowLift (b : Fin w →₀ ℕ) :
    ConvolutionFree.Target K t 0 d →ₗ[K] ConvolutionFree.Target K t w (d + b.degree) :=
  LinearMap.pi fun r =>
    (((liftCoeff b).comp (Quartic.Forms K t d).subtype).codRestrict _
      (fun p => liftCoeff_homogeneous b p.val p.property)).comp (LinearMap.proj r)

@[simp] theorem rowLift_apply_val (b : Fin w →₀ ℕ)
    (v : ConvolutionFree.Target K t 0 d) (r : Fin 3) :
    (rowLift b v r).val = liftCoeff b (v r).val := rfl

/-- Extract the same free monomial from the degree in which it was inserted. -/
def rowCoeff (b : Fin w →₀ ℕ) :
    ConvolutionFree.Target K t w (d + b.degree) →ₗ[K] ConvolutionFree.Target K t 0 d :=
  LinearMap.pi fun r =>
    (((freeCoeff b).comp (Quartic.Forms K (t + w) (d + b.degree)).subtype).codRestrict _
      (fun p => by
        change (freeCoeff b p.val).IsHomogeneous d
        simpa only [Nat.add_sub_cancel] using freeCoeff_homogeneous p.val p.property b)).comp
      (LinearMap.proj r)

@[simp] theorem rowCoeff_apply_val (b : Fin w →₀ ℕ)
    (v : ConvolutionFree.Target K t w (d + b.degree)) (r : Fin 3) :
    (rowCoeff b v r).val = freeCoeff b (v r).val := rfl

theorem rowLift_maps_relations (b : Fin w →₀ ℕ) :
    relations K t 0 d ≤ (relations K t w (d + b.degree)).comap (rowLift b) := by
  rintro v ⟨a, ha⟩
  refine ⟨fun s => liftCoeff b (a s), ?_⟩
  funext r
  rw [polyPresentation_liftCoeff, ha]
  rfl

theorem rowCoeff_maps_relations (b : Fin w →₀ ℕ) :
    relations K t w (d + b.degree) ≤ (relations K t 0 d).comap (rowCoeff b) := by
  rintro v ⟨a, ha⟩
  refine ⟨fun s => freeCoeff b (a s), ?_⟩
  funext r
  rw [← polyPresentation_freeCoeff, ha]
  rfl

/-- Insert a core quotient class at a specified free monomial. -/
def pieceLift (b : Fin w →₀ ℕ) : Piece K t 0 d →ₗ[K] Piece K t w (d + b.degree) :=
  Submodule.mapQ _ _ (rowLift b) (rowLift_maps_relations b)

/-- Project onto the core quotient class at a specified free monomial. -/
def pieceCoeff (b : Fin w →₀ ℕ) : Piece K t w (d + b.degree) →ₗ[K] Piece K t 0 d :=
  Submodule.mapQ _ _ (rowCoeff b) (rowCoeff_maps_relations b)

@[simp] theorem pieceLift_mk (b : Fin w →₀ ℕ) (v : ConvolutionFree.Target K t 0 d) :
    pieceLift b (Submodule.Quotient.mk v) = Submodule.Quotient.mk (rowLift b v) := rfl

@[simp] theorem pieceCoeff_mk (b : Fin w →₀ ℕ)
    (v : ConvolutionFree.Target K t w (d + b.degree)) :
    pieceCoeff b (Submodule.Quotient.mk v) = Submodule.Quotient.mk (rowCoeff b v) := rfl

@[simp] theorem rowCoeff_rowLift (b : Fin w →₀ ℕ) (v : ConvolutionFree.Target K t 0 d) :
    rowCoeff b (rowLift b v) = v := by
  funext r
  apply Subtype.ext
  simp [freeCoeff_liftCoeff]

/-- Free-monomial insertion is split by the actual coefficient projection. -/
@[simp] theorem pieceCoeff_pieceLift (b : Fin w →₀ ℕ) (v : Piece K t 0 d) :
    pieceCoeff b (pieceLift b v) = v := by
  refine Submodule.Quotient.induction_on _ v ?_
  intro v
  simp

theorem pieceLift_injective (b : Fin w →₀ ℕ) :
    Function.Injective (pieceLift (K := K) (t := t) (d := d) b) :=
  Function.LeftInverse.injective (pieceCoeff_pieceLift b)

/-- Renaming the core variables inserts zero exponents at all free variables. -/
theorem core_rename_exponent (a : Fin t →₀ ℕ) :
    a.mapDomain (Fin.castAdd w) = mergeExponent a 0 := by
  ext s
  refine Fin.addCases ?_ ?_ s
  · intro i
    rw [Finsupp.mapDomain_apply_of_injective (Fin.castAdd_injective t w)]
    simp
  · intro i
    rw [Finsupp.mapDomain_of_notMem_range]
    · simp
    · rintro ⟨l, hl⟩
      have h := congrArg Fin.val hl
      simp at h
      omega

/-- Insertion is exactly multiplication by the corresponding free monomial. -/
theorem liftCoeff_eq_mul (b : Fin w →₀ ℕ) (p : Quartic.Poly K t) :
    liftCoeff b p =
      rename (Fin.castAdd w) p * monomial (mergeExponent (0 : Fin t →₀ ℕ) b) 1 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
      have he : mergeExponent a b = mergeExponent a 0 + mergeExponent 0 b := by
        ext s
        refine Fin.addCases ?_ ?_ s <;> intro i <;> simp
      simp only [liftCoeff_monomial, rename_monomial, core_rename_exponent,
        monomial_mul_monomial, mul_one, he]
  | add p q hp hq => simp [hp, hq, add_mul]

/-- In degree zero of the free variables, insertion is the ordinary core renaming. -/
theorem liftCoeff_zero_eq_rename (p : Quartic.Poly K t) :
    liftCoeff (0 : Fin w →₀ ℕ) p = rename (Fin.castAdd w) p := by
  rw [liftCoeff_eq_mul]
  have he : mergeExponent (0 : Fin t →₀ ℕ) (0 : Fin w →₀ ℕ) = 0 := by
    ext s
    refine Fin.addCases ?_ ?_ s <;> intro i <;> simp
  simp [he]

/-- The actual homogeneous polynomial associated to a free exponent vector. -/
def freeMonomial (b : Fin w →₀ ℕ) : Quartic.Forms K (t + w) b.degree :=
  ⟨monomial (mergeExponent (0 : Fin t →₀ ℕ) b) 1,
    isHomogeneous_monomial 1 (by simp)⟩

/-- Inserting a free component is ordinary multiplication of the embedded core row. -/
theorem rowLift_eq_mul (b : Fin w →₀ ℕ) (v : ConvolutionFree.Target K t 0 d) :
    rowLift b v = rowMul (freeMonomial b) (rowLift (0 : Fin w →₀ ℕ) v) := by
  funext r
  apply Subtype.ext
  simp only [rowLift_apply_val, rowMul_apply_val, liftCoeff_zero_eq_rename]
  rw [liftCoeff_eq_mul]
  exact mul_comm _ _

/-- The split summand insertion really is multiplication by its free monomial. -/
theorem pieceLift_eq_mul (b : Fin w →₀ ℕ) (x : Piece K t 0 d) :
    pieceLift b x = pieceMul (freeMonomial b) (pieceLift (0 : Fin w →₀ ℕ) x) := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  simp only [pieceLift_mk, pieceMul_mk]
  exact congrArg (relations K t w (d + b.degree)).mkQ (rowLift_eq_mul b v)

end Quartic.ConvolutionFreeMultiplication
