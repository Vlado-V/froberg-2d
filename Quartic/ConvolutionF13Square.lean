module

public import Quartic.ConvolutionCubicGeneric
public import Quartic.QuotientExchange
public import Mathlib.LinearAlgebra.Quotient.Pi

@[expose] public section

/-! # The actual convolution quotient-exchange square -/
noncomputable section
namespace Quartic.ConvolutionF13Square
open Module MvPolynomial ConvolutionFreePieces ConvolutionFreeMultiplication
open ConvolutionOuterIncidence
variable {K : Type*} [Field K] {t w q : ℕ}

abbrev Top (K : Type*) [Field K] (t w : ℕ) := ConvolutionFree.Source K t w 2
abbrev Bottom (K : Type*) [Field K] (t w q : ℕ) := Fin q → ConvolutionFree.Target K t w 1
abbrev Corner (K : Type*) [Field K] (t w q : ℕ) := Fin q → ConvolutionFree.Source K t w 0
abbrev Ambient (K : Type*) [Field K] (t w : ℕ) := ConvolutionFree.Target K t w 3

/-- Multiply a quadratic tuple by homogeneous constants and add. -/
def quadraticCombination (Q : Coefficients K t w q) :
    (Fin q → Forms K (t+w) 0) →ₗ[K] Forms K (t+w) 2 :=
  ∑ j, (formMul (Q j)).comp (LinearMap.proj j)

@[simp] theorem quadraticCombination_val (Q : Coefficients K t w q)
    (z : Fin q → Forms K (t+w) 0) :
    (quadraticCombination Q z).val = ∑ j, (Q j).val * (z j).val := by
  simp [quadraticCombination, formMul]

/-- Apply one tuple map separately in every coordinate. -/
def rowwise {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module K A] [Module K B] (n : ℕ) (f : (Fin q → A) →ₗ[K] B) :
    (Fin q → Fin n → A) →ₗ[K] (Fin n → B) where
  toFun z r := f (fun j => z j r)
  map_add' x y := by funext r; exact f.map_add _ _
  map_smul' s x := by funext r; exact f.map_smul s _

/-- The top horizontal multiplication by the actual quadrics. -/
def topRelations (Q : Coefficients K t w q) : Corner K t w q →ₗ[K] Top K t w :=
  rowwise (t+2) (quadraticCombination Q)

/-- The right-hand cubic multiplication, one actual map in every output row. -/
def bottomMultiplication (Q : Coefficients K t w q) : Bottom K t w q →ₗ[K] Ambient K t w :=
  rowwise 3 (CubicGeneric.cubicMap Q)

/-- The degree-zero convolution presentation in each tuple component. -/
def cornerPresentation : Corner K t w q →ₗ[K] Bottom K t w q :=
  LinearMap.pi fun j => ConvolutionFree.presentation.comp (LinearMap.proj j)

@[simp] theorem topRelations_val (Q : Coefficients K t w q) (z : Corner K t w q)
    (k : Fin (t+2)) :
    (topRelations Q z k).val = ∑ j, (Q j).val * (z j k).val := quadraticCombination_val Q _

@[simp] theorem bottomMultiplication_val (Q : Coefficients K t w q) (v : Bottom K t w q)
    (r : Fin 3) :
    (bottomMultiplication Q v r).val = ∑ j, (v j r).val * (Q j).val := CubicGeneric.cubicMap_val Q _

@[simp] theorem cornerPresentation_apply (z : Corner K t w q) (j : Fin q) :
    cornerPresentation z j = ConvolutionFree.presentation (z j) := rfl

/-- The square commutes by the actual polynomial products. -/
theorem square_commutes (Q : Coefficients K t w q) :
    ConvolutionFree.presentation.comp (topRelations Q) =
      (bottomMultiplication Q).comp cornerPresentation := by
  apply LinearMap.ext
  intro z
  funext r
  apply Subtype.ext
  simp only [LinearMap.comp_apply, ConvolutionFree.presentation_apply_val,
    topRelations_val, bottomMultiplication_val, cornerPresentation_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Pass each actual degree-one row vector to its quotient class. -/
def tupleClasses : Bottom K t w q →ₗ[K] SourceTuple K t w q :=
  LinearMap.pi fun j => (relations K t w 1).mkQ.comp (LinearMap.proj j)

/-- Its kernel is precisely the tuple of degree-zero presentations. -/
theorem tupleClasses_kernel : LinearMap.ker (tupleClasses (K := K) (t := t) (w := w) (q := q)) =
    LinearMap.range cornerPresentation := by
  classical
  ext v
  constructor
  · intro hv
    have h : ∀ j, ∃ z : ConvolutionFree.Source K t w 0,
        ConvolutionFree.presentation z = v j := by
      intro j
      have hj : v j ∈ relations K t w 1 := by
        apply (Submodule.Quotient.mk_eq_zero _).mp
        exact congrFun hv j
      rwa [relations_succ] at hj
    choose z hz using h
    exact ⟨z, funext hz⟩
  · rintro ⟨z, rfl⟩
    ext j
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rw [relations_succ]
    exact ⟨z j, rfl⟩

/-- The lower map modulo the convolution relations is exactly outer multiplication. -/
theorem outer_square (Q : Coefficients K t w q) (v : Bottom K t w q) :
    (relations K t w 3).mkQ (bottomMultiplication Q v) = outerMap Q (tupleClasses v) := by
  rw [outerMap_apply]
  change (relations K t w 3).mkQ (bottomMultiplication Q v) =
    ∑ j, (relations K t w 3).mkQ (rowMul (Q j) (v j))
  rw [← map_sum]
  apply congrArg (relations K t w 3).mkQ
  funext r
  apply Subtype.ext
  simp only [bottomMultiplication_val, Finset.sum_apply, AddSubmonoidClass.coe_finsetSum,
    rowMul_apply_val]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- Outer injectivity supplies the exactness hypothesis of quotient exchange. -/
theorem lower_kernel_le (Q : Coefficients K t w q) (hQ : Function.Injective (outerMap Q)) :
    LinearMap.ker ((LinearMap.range (ConvolutionFree.presentation (K := K) (t := t)
      (w := w) (j := 2))).mkQ.comp (bottomMultiplication Q)) ≤
        LinearMap.range cornerPresentation := by
  intro v hv
  have hz : (relations K t w 3).mkQ (bottomMultiplication Q v) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rw [relations_succ]
    exact (Submodule.Quotient.mk_eq_zero _).mp hv
  rw [outer_square] at hz
  rw [← tupleClasses_kernel]
  exact hQ (hz.trans (map_zero _).symm)

/-- The presentation after quotienting the two actual quadratic images. -/
def exchangeMap (Q : Coefficients K t w q) :
    Top K t w ⧸ LinearMap.range (topRelations Q) →ₗ[K]
      Ambient K t w ⧸ LinearMap.range (bottomMultiplication Q) :=
  QuotientExchange.quotientMap ConvolutionFree.presentation (bottomMultiplication Q)
    (topRelations Q) cornerPresentation (square_commutes Q)

@[simp] theorem exchangeMap_mk (Q : Coefficients K t w q) (u : Top K t w) :
    exchangeMap Q (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (ConvolutionFree.presentation u) := rfl

/-- This actual quotient presentation is injective whenever outer multiplication is. -/
theorem exchangeMap_injective (ht : 2 ≤ t) (Q : Coefficients K t w q)
    (hQ : Function.Injective (outerMap Q)) : Function.Injective (exchangeMap Q) :=
  QuotientExchange.quotientMap_injective _ _ _ _
    (ConvolutionFree.presentation_injective ht (by decide : 2 ≤ 2))
    (square_commutes Q) (lower_kernel_le Q hQ)

end Quartic.ConvolutionF13Square
