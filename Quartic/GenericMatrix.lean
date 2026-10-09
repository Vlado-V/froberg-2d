module

public import Quartic.Multiplication
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

/-!
# Polynomial multiplication matrices and a concrete generic-open criterion

The entries below are polynomials in the ordered quadratic coefficients.
Specialization gives the matrix of actual polynomial multiplication. Two
nonzero minors at one coefficient array then supply a nonempty principal open:
one minor certifies independent generators and the other certifies enough
multiplication rank to attain the universal quotient lower bound.
-/

noncomputable section

namespace Quartic

open Module MvPolynomial

variable {K : Type*} [Field K] {n r : ℕ}

/-- Coordinates of a tuple of homogeneous quadratic multipliers. -/
def multiplierCoordinates : (Fin r → Forms K n 2) ≃ₗ[K] (CoefficientIndex n r → K) where
  toFun f im := (formsBasis K n 2).equivFun (f im.1) im.2
  invFun a := coefficientQuadrics K n r a
  left_inv f := by
    funext i
    exact (formsBasis K n 2).equivFun.symm_apply_apply (f i)
  right_inv a := by
    funext im
    exact congrFun ((formsBasis K n 2).equivFun.apply_symm_apply (fun m => a (im.1, m))) im.2
  map_add' f g := by ext im; simp
  map_smul' c f := by ext im; simp

/-- The multiplier basis indexed by a generator and a quadratic monomial. -/
def multiplierBasis : Basis (CoefficientIndex n r) K (Fin r → Forms K n 2) :=
  Basis.ofEquivFun multiplierCoordinates

/-- The multiplication map depends linearly on the generator coefficients. -/
def coefficientMultiplicationLinear : (CoefficientIndex n r → K) →ₗ[K]
    ((Fin r → Forms K n 2) →ₗ[K] Forms K n 4) where
  toFun a := quadraticMultiplication (coefficientQuadrics K n r a)
  map_add' a b := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    simp [quadraticMultiplication_val, coefficientQuadrics, add_smul, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    simp [quadraticMultiplication_val, coefficientQuadrics, mul_smul, ← Finset.smul_sum]

/-- The actual matrix of multiplication after choosing a coefficient array. -/
def multiplicationMatrixLinear : (CoefficientIndex n r → K) →ₗ[K]
    Matrix (Sym (Fin n) 4) (CoefficientIndex n r) K :=
  (LinearMap.toMatrix (multiplierBasis (K := K)) (formsBasis K n 4)).toLinearMap.comp
    coefficientMultiplicationLinear

/-- A scalar linear function encoded as a homogeneous linear polynomial. -/
def polynomialOfLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → K) →ₗ[K] K) : MvPolynomial ι K :=
  ∑ i, C (L (Pi.single i 1)) * X i

theorem eval_polynomialOfLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → K) →ₗ[K] K) (a : ι → K) :
    eval a (polynomialOfLinear L) = L a := by
  have h := congrArg L ((Pi.basisFun K ι).sum_equivFun a)
  simpa [polynomialOfLinear, map_sum, Pi.basisFun_apply, Pi.basisFun_equivFun,
    smul_eq_mul, mul_comm] using h

/-- One entry of the actual matrix, as a linear function of all coefficients. -/
def multiplicationEntryLinear (row : Sym (Fin n) 4) (col : CoefficientIndex n r) :
    (CoefficientIndex n r → K) →ₗ[K] K where
  toFun a := multiplicationMatrixLinear a row col
  map_add' a b := by simp
  map_smul' c a := by simp

/-- A matrix over the polynomial ring in all quadratic generator coefficients. -/
def genericMultiplicationMatrix :
    Matrix (Sym (Fin n) 4) (CoefficientIndex n r)
      (MvPolynomial (CoefficientIndex n r) K) :=
  fun row col => polynomialOfLinear (multiplicationEntryLinear row col)

/-- Specializing the symbolic matrix gives the actual quadratic multiplication matrix. -/
theorem genericMultiplicationMatrix_specialize (a : CoefficientIndex n r → K) :
    (genericMultiplicationMatrix (K := K)).map (eval a) = multiplicationMatrixLinear a := by
  ext row col
  exact eval_polynomialOfLinear (multiplicationEntryLinear row col) a

/-- Matrix rank is the intrinsic dimension of the multiplication image. -/
theorem multiplicationMatrix_rank (a : CoefficientIndex n r → K) :
    (multiplicationMatrixLinear a).rank =
      finrank K (LinearMap.range (quadraticMultiplication (coefficientQuadrics K n r a))) := by
  rw [Matrix.rank_eq_finrank_range_toLin (multiplicationMatrixLinear a)
    (formsBasis K n 4) multiplierBasis]
  change finrank K (LinearMap.range
    (Matrix.toLin multiplierBasis (formsBasis K n 4)
      (LinearMap.toMatrix multiplierBasis (formsBasis K n 4)
        (quadraticMultiplication (coefficientQuadrics K n r a))))) = _
  rw [Matrix.toLin_toMatrix]

/-- A selected square coefficient matrix for the ordered quadratic generators. -/
def coefficientMinor (selected : Fin r → Sym (Fin n) 2) :
    MvPolynomial (CoefficientIndex n r) K :=
  Matrix.det (Matrix.of fun i j => (X (i, selected j) :
    MvPolynomial (CoefficientIndex n r) K))

theorem eval_coefficientMinor (selected : Fin r → Sym (Fin n) 2)
    (a : CoefficientIndex n r → K) :
    eval a (coefficientMinor selected) =
      Matrix.det (Matrix.of fun i j => a (i, selected j)) := by
  unfold coefficientMinor
  rw [(eval a).map_det]
  congr 1
  ext i j
  simp

/-- A nonzero coefficient minor proves independence of the actual polynomial generators. -/
theorem coefficient_independent_of_minor (selected : Fin r → Sym (Fin n) 2)
    (a : CoefficientIndex n r → K)
    (hdet : Matrix.det (Matrix.of fun i j => a (i, selected j)) ≠ 0) :
    LinearIndependent K (fun i => (coefficientQuadrics K n r a i).val) := by
  have hrows := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  let L : Forms K n 2 →ₗ[K] (Fin r → K) :=
    LinearMap.pi (fun j => (LinearMap.proj (selected j)).comp
      (formsBasis K n 2).equivFun.toLinearMap)
  have hlin : LinearIndependent K (coefficientQuadrics K n r a) := by
    apply LinearIndependent.of_comp L
    have heq : L ∘ coefficientQuadrics K n r a = (fun i j => a (i, selected j)) := by
      funext i j
      change (formsBasis K n 2).equivFun
        ((formsBasis K n 2).equivFun.symm (fun m => a (i, m))) (selected j) = _
      simp only [LinearEquiv.apply_symm_apply]
    rw [heq]
    exact hrows
  exact hlin.map' (Forms K n 2).subtype
    (LinearMap.ker_eq_bot.mpr (Submodule.injective_subtype _))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A selected square multiplication minor, as one polynomial in all coefficients. -/
def multiplicationMinor (rows : ι → Sym (Fin n) 4) (cols : ι → CoefficientIndex n r) :
    MvPolynomial (CoefficientIndex n r) K :=
  ((genericMultiplicationMatrix (K := K)).submatrix rows cols).det

theorem eval_multiplicationMinor (rows : ι → Sym (Fin n) 4)
    (cols : ι → CoefficientIndex n r) (a : CoefficientIndex n r → K) :
    eval a (multiplicationMinor rows cols) =
      ((multiplicationMatrixLinear a).submatrix rows cols).det := by
  unfold multiplicationMinor
  rw [(eval a).map_det]
  change (((genericMultiplicationMatrix (K := K)).map (eval a)).submatrix rows cols).det = _
  rw [genericMultiplicationMatrix_specialize]

/-- A numerical nonzero minor forces the corresponding intrinsic multiplication rank. -/
theorem multiplication_rank_of_minor (rows : ι → Sym (Fin n) 4)
    (cols : ι → CoefficientIndex n r) (a : CoefficientIndex n r → K)
    (hdet : ((multiplicationMatrixLinear a).submatrix rows cols).det ≠ 0) :
    Fintype.card ι ≤
      finrank K (LinearMap.range (quadraticMultiplication (coefficientQuadrics K n r a))) := by
  calc
    Fintype.card ι = ((multiplicationMatrixLinear a).submatrix rows cols).rank :=
      (Matrix.rank_of_det_ne_zero hdet).symm
    _ ≤ (multiplicationMatrixLinear a).rank := Matrix.rank_submatrix_le _ rows cols
    _ = _ := multiplicationMatrix_rank a

/-- Two concrete nonzero witness minors yield the manuscript's actual generic
quotient-dimension statement on one nonempty principal open. -/
theorem genericQuartic_of_nonzero_minors
    (selected : Fin r → Sym (Fin n) 2)
    (rows : ι → Sym (Fin n) 4) (cols : ι → CoefficientIndex n r)
    (a₀ : CoefficientIndex n r → K)
    (hcoeff : Matrix.det (Matrix.of fun i j => a₀ (i, selected j)) ≠ 0)
    (hmult : ((multiplicationMatrixLinear a₀).submatrix rows cols).det ≠ 0)
    (hsize : (n + 3).choose 4 ≤ Fintype.card ι + expectedDimension n r) :
    GenericQuartic K n r := by
  refine ⟨coefficientMinor selected * multiplicationMinor rows cols, ⟨a₀, ?_⟩, ?_⟩
  · simpa only [map_mul, eval_coefficientMinor, eval_multiplicationMinor] using
      mul_ne_zero hcoeff hmult
  · intro a ha
    have hparts :
        Matrix.det (Matrix.of fun i j => a (i, selected j)) ≠ 0 ∧
        ((multiplicationMatrixLinear a).submatrix rows cols).det ≠ 0 := by
      simpa only [map_mul, eval_coefficientMinor, eval_multiplicationMinor,
        mul_ne_zero_iff] using ha
    have hlin := coefficient_independent_of_minor selected a hparts.1
    have hlower := coefficient_quotient_lower_bound a hlin
    have hrank := multiplication_rank_of_minor rows cols a hparts.2
    have hdim := quartic_quotient_add_rank (coefficientQuadrics K n r a)
    change finrank K (QuarticQuotient K n (coefficientSpace K n r a)) +
      finrank K (LinearMap.range (quadraticMultiplication (coefficientQuadrics K n r a))) =
        (n + 3).choose 4 at hdim
    exact ⟨hlin, by omega⟩

end Quartic
