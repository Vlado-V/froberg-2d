module

public import Quartic.ConvolutionMultiplication

@[expose] public section

/-!
# Evaluated contraction on the actual convolution dual

Evaluating the second ordinary slot of the degree-two dual corresponds to
contracting by the linear form whose coefficients are `(1,a,...,a^(t-1))`.
This is the uniform contraction operation entering the sharp image bound.
-/

noncomputable section
namespace Quartic.ConvolutionEvaluation
open MvPolynomial ConvolutionPresentation ConvolutionDual ConvolutionTuples
open ConvolutionFactor ConvolutionSlots ConvolutionInverse ConvolutionMultiplication
variable {K : Type*} [Field K] {t : ℕ}

/-- Set the second ordinary slot to the scalar `a`. -/
def evaluateSecond (a : K) : Slots K 2 →ₐ[K] Slots K 1 :=
  aeval fun o => o.elim (X none)
    (fun i => if i = 0 then X (some 0) else C a)

/-- A rectangular exponent represents the corresponding separate powers. -/
theorem monomial_slotExponent {j : ℕ} (d : ℕ) (v : Fin j → ℕ) (c : K) :
    (monomial (slotExponent d v) c : Slots K j) =
      C c * ((X none) ^ d * ∏ i : Fin j, (X (some i)) ^ v i) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp [Fintype.prod_option, slotExponent]
  · intro i
    simp

/-- Evaluation removes a slot and weights its exponent by the corresponding power. -/
theorem evaluateSecond_monomial (a : K) (d : ℕ) (v : Fin 2 → ℕ) (c : K) :
    evaluateSecond a (monomial (slotExponent d v) c) =
      monomial (slotExponent d (fun _ : Fin 1 => v 0)) (c * a ^ v 1) := by
  rw [monomial_slotExponent, map_mul, map_mul, map_pow, map_prod]
  simp only [evaluateSecond, aeval_C, aeval_X, Option.elim_none, Option.elim_some,
    Fin.prod_univ_two, map_pow]
  simp only [ite_eq_left, one_ne_zero, ite_false, MvPolynomial.algebraMap_eq]
  rw [monomial_slotExponent]
  simp only [Fin.prod_univ_one, map_mul, map_pow]
  ring

/-- The actual variable as a homogeneous linear polynomial. -/
def variableForm (i : Fin t) : Quartic.Forms K t 1 :=
  ⟨X i, isHomogeneous_X K i⟩

/-- Variable multiplication on a row monomial is ordinary exponent addition. -/
theorem targetMul_variable_rowMonomial {j : ℕ} (i : Fin t) (d : Fin 3)
    (e : Fin t →₀ ℕ) (he : e.degree = j) :
    targetMul (variableForm (K := K) i) (rowMonomial d e he) =
      rowMonomial d (e + Finsupp.single i 1) (degree_add_single e he i) := by
  classical
  funext r
  apply Subtype.ext
  by_cases h : r = d
  · subst r
    simp [targetMul, formMul, variableForm, rowMonomial, monomialForm,
      X, monomial_mul_monomial, add_comm]
  · simp [targetMul, formMul, variableForm, rowMonomial, h]

/-- The evaluated contraction is a linear combination of actual multiplication transposes. -/
def evaluatedContract (a : K) (φ : annihilator K t 1) : annihilator K t 0 :=
  ∑ i : Fin t, a ^ i.val • dualContract (variableForm i) φ

@[simp] theorem evaluatedContract_rowMonomial (a : K) (φ : annihilator K t 1)
    (d : Fin 3) (v : Fin 1 → Fin t) :
    (evaluatedContract a φ).val
      (rowMonomial d (tupleExponent v) (tupleExponent_degree v)) =
      ∑ i : Fin t, a ^ i.val * φ.val
        (rowMonomial d (tupleExponent v + Finsupp.single i 1)
          (degree_add_single (tupleExponent v) (tupleExponent_degree v) i)) := by
  simp only [evaluatedContract, Submodule.coe_sum, Submodule.coe_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change φ.val (targetMul (variableForm i) _) = _
  rw [targetMul_variable_rowMonomial]

/-- The one-slot encoding written as its row and variable coefficient sum. -/
theorem encode_one (φ : Module.Dual K (Target K t 1)) :
    encode φ = ∑ d : Fin 3, ∑ i : Fin t,
      monomial (slotExponent d.val (fun _ : Fin 1 => i.val))
        (φ (rowMonomial d (tupleExponent (fun _ : Fin 1 => i))
          (tupleExponent_degree _))) := by
  classical
  rw [encode, ofCoefficients, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin t)).symm]
  rfl

/-- The two-slot encoding written with both independent variable indices. -/
theorem encode_two (φ : Module.Dual K (Target K t 2)) :
    encode φ = ∑ d : Fin 3, ∑ i : Fin t, ∑ k : Fin t,
      monomial (slotExponent d.val (fun l => (![i, k] l).val))
        (φ (rowMonomial d (tupleExponent ![i, k]) (tupleExponent_degree _))) := by
  classical
  rw [encode, ofCoefficients, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Equiv.sum_comp (finTwoArrowEquiv (Fin t)).symm, Fintype.sum_prod_type]
  rfl

/-- Evaluation of the encoded degree-two dual is exactly evaluated actual contraction. -/
theorem encode_evaluatedContract (a : K) (φ : annihilator K t 1) :
    encode (evaluatedContract a φ).val = evaluateSecond a (encode φ.val) := by
  classical
  rw [encode_one, encode_two]
  simp only [map_sum, evaluateSecond_monomial, evaluatedContract_rowMonomial]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_comm]
  congr 2
  congr 2
  simp [tupleExponent, Fin.sum_univ_two]

/-- The degree-two diagonal factor evaluates to the degree-one factor times `s-a`. -/
theorem evaluateSecond_diagonalProduct (a : K) :
    evaluateSecond a (diagonalProduct K 2) =
      diagonalProduct K 1 * (X none - C a) := by
  simp [diagonalProduct, Fin.prod_univ_two, evaluateSecond]

/-- Removing the common first diagonal factor gives the precise evaluated
contraction formula used by the uniform shadow estimate. -/
theorem inverseFactor_evaluatedContract (a : K) (φ : annihilator K t 1) :
    inverseFactor (evaluatedContract a φ) =
      (X none - C a) * evaluateSecond a (inverseFactor φ) := by
  apply mul_left_cancel₀ (diagonalProduct_ne_zero K 1)
  rw [← inverseFactor_spec, encode_evaluatedContract, inverseFactor_spec,
    map_mul, evaluateSecond_diagonalProduct, mul_assoc]

end Quartic.ConvolutionEvaluation
