import Quartic.FourVariables

/-!
# Complete five-variable endpoint witnesses

Five coordinate squares yield 65 independent quartics. Modulo their products,
the five cycle-edge multiples of the sum of the ten mixed quadratic monomials
have coefficient matrix of determinant three. Its explicit integer inverse
clears the remaining five squarefree quartics in characteristic zero.
-/

noncomputable section

namespace Quartic.FiveVariables

open MvPolynomial Module SmallCases

variable {K : Type*} [Field K]

def exponent (a b c d e : ℕ) : Fin 5 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c +
    Finsupp.single 3 d + Finsupp.single 4 e

def quadraticExponents : Fin 15 → (Fin 5 →₀ ℕ) := ![exponent 2 0 0 0 0, exponent 0 2 0 0 0, exponent 0 0 2 0 0, exponent 0 0 0 2 0, exponent 0 0 0 0 2, exponent 1 1 0 0 0, exponent 1 0 1 0 0, exponent 1 0 0 1 0, exponent 1 0 0 0 1, exponent 0 1 1 0 0, exponent 0 1 0 1 0, exponent 0 1 0 0 1, exponent 0 0 1 1 0, exponent 0 0 1 0 1, exponent 0 0 0 1 1]

theorem quadraticExponents_degree (i : Fin 15) : (quadraticExponents i).degree = 2 := by
  fin_cases i <;> simp [quadraticExponents, exponent]

def encode (e : Fin 5 →₀ ℕ) : ℕ :=
  e 0 + 5 * e 1 + 25 * e 2 + 125 * e 3 + 625 * e 4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem quadraticExponents_injective : Function.Injective quadraticExponents := by
  have heq : (fun i => encode (quadraticExponents i)) = ![2, 10, 50, 250, 1250, 6, 26, 126, 626, 30, 130, 630, 150, 650, 750] := by
    funext i
    fin_cases i <;> norm_num [encode, quadraticExponents, exponent]
  have h : Function.Injective (fun i => encode (quadraticExponents i)) := by
    rw [heq]; decide +kernel
  intro i j hij
  exact h (congrArg encode hij)

def productGenerators : Fin 65 → Fin 5 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4]
def productMultipliers : Fin 65 → Fin 15 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def squareProductExponents (i : Fin 65) : Fin 5 →₀ ℕ :=
  quadraticExponents (Fin.castLE (by decide : 5 ≤ 15) (productGenerators i)) +
    quadraticExponents (productMultipliers i)

theorem squareProductExponents_degree (i : Fin 65) : (squareProductExponents i).degree = 4 := by
  simp [squareProductExponents, quadraticExponents_degree]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem squareProductExponents_injective : Function.Injective squareProductExponents := by
  have heq : (fun i => encode (squareProductExponents i)) = ![4, 12, 52, 252, 1252, 8, 28, 128, 628, 32, 132, 632, 152, 652, 752, 20, 60, 260, 1260, 16, 36, 136, 636, 40, 140, 640, 160, 660, 760, 100, 300, 1300, 56, 76, 176, 676, 80, 180, 680, 200, 700, 800, 500, 1500, 256, 276, 376, 876, 280, 380, 880, 400, 900, 1000, 2500, 1256, 1276, 1376, 1876, 1280, 1380, 1880, 1400, 1900, 2000] := by
    funext i
    fin_cases i <;> norm_num [encode, squareProductExponents, productGenerators,
      productMultipliers, quadraticExponents, exponent]
  have h : Function.Injective (fun i => encode (squareProductExponents i)) := by
    rw [heq]; decide +kernel
  intro i j hij
  exact h (congrArg encode hij)

/-- Five squares attain the expected five-dimensional quartic quotient. -/
theorem witness_five_squares : QuarticWitness K 5 5 := by
  exact witness_of_monomial_products
    (q := quadraticExponents ∘ Fin.castLE (by decide : 5 ≤ 15))
    (e := squareProductExponents)
    (generator := productGenerators)
    (multiplier := quadraticExponents ∘ productMultipliers)
    (hq := fun i => quadraticExponents_degree _)
    (hiq := quadraticExponents_injective.comp (Fin.castLE_injective _))
    (he := squareProductExponents_degree)
    (hie := squareProductExponents_injective)
    (hm := fun i => quadraticExponents_degree _)
    (hproduct := fun i => rfl)
    (hsize := by norm_num [expectedDimension, Nat.choose])

def squarefreeExponents : Fin 5 → (Fin 5 →₀ ℕ) := ![exponent 0 1 1 1 1, exponent 1 0 1 1 1, exponent 1 1 0 1 1, exponent 1 1 1 0 1, exponent 1 1 1 1 0]

theorem squarefreeExponents_degree (i : Fin 5) : (squarefreeExponents i).degree = 4 := by
  fin_cases i <;> simp [squarefreeExponents, exponent]

def quadratic (i : Fin 15) : Poly K 5 := monomial (quadraticExponents i) 1
def mixed : Poly K 5 := ∑ i : Fin 10, quadratic ⟨i.val + 5, by omega⟩
def squarefree (i : Fin 5) : Poly K 5 := monomial (squarefreeExponents i) 1

def generatorPolys : Fin 6 → Poly K 5 :=
  ![quadratic 0, quadratic 1, quadratic 2, quadratic 3, quadratic 4, mixed]

theorem quadratic_homogeneous (i : Fin 15) : IsHomogeneous (quadratic (K := K) i) 2 :=
  isHomogeneous_monomial 1 (quadraticExponents_degree i)

theorem mixed_homogeneous : IsHomogeneous (mixed (K := K)) 2 := by
  exact (Forms K 5 2).sum_mem fun i _ => quadratic_homogeneous _

def generators (i : Fin 6) : Forms K 5 2 :=
  ⟨generatorPolys i, by
    fin_cases i <;> first | exact quadratic_homogeneous _ | exact mixed_homogeneous⟩

def separatingExponents : Fin 6 → (Fin 5 →₀ ℕ) :=
  ![quadraticExponents 0, quadraticExponents 1, quadraticExponents 2,
    quadraticExponents 3, quadraticExponents 4, quadraticExponents 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem separating_coefficients (i j : Fin 6) :
    (generatorPolys (K := K) j).coeff (separatingExponents i) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [generatorPolys, separatingExponents, mixed, quadratic,
      quadraticExponents, exponent, Fin.sum_univ_succ, coeff_monomial,
      Finsupp.ext_iff, Fin.forall_fin_succ]

theorem generators_independent : LinearIndependent K (generators (K := K)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h := congrArg (fun p : Forms K 5 2 => p.val.coeff (separatingExponents i)) hc
  simpa [Submodule.coe_sum, Submodule.coe_smul, coeff_sum, coeff_smul,
    generators, separating_coefficients, Submodule.coe_zero, AddMonoidAlgebra.coeff_zero,
    Pi.zero_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] using h

def generatorSpace : Submodule K (Poly K 5) :=
  Submodule.span K (Set.range (generatorPolys (K := K)))

theorem square_mem_generatorSpace (i : Fin 5) :
    quadratic (K := K) (Fin.castLE (by decide : 5 ≤ 15) i) ∈ generatorSpace := by
  have h : quadratic (K := K) (Fin.castLE (by decide : 5 ≤ 15) i) =
      generatorPolys (Fin.castLE (by decide : 5 ≤ 6) i) := by fin_cases i <;> rfl
  rw [h]
  exact Submodule.subset_span ⟨_, rfl⟩

theorem mixed_mem_generatorSpace : mixed (K := K) ∈ generatorSpace :=
  Submodule.subset_span ⟨5, rfl⟩

def cycleEdges : Fin 5 → Fin 15 := ![5, 9, 12, 14, 8]

def residualMatrix : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, 0, 1, 1, 1; 1, 0, 0, 1, 1; 1, 1, 0, 0, 1;
    1, 1, 1, 0, 0; 0, 1, 1, 1, 0]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem residualMatrix_det : residualMatrix.det = 3 := by
  norm_num [residualMatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix, Fin.succAbove]

def correctionGenerators : Fin 5 → Fin 7 → Fin 5 := ![![0, 0, 0, 0, 1, 1, 1], ![1, 2, 1, 1, 1, 2, 2], ![2, 3, 2, 3, 2, 2, 3], ![3, 4, 3, 4, 3, 4, 3], ![0, 0, 0, 0, 4, 4, 4]]
def correctionMultipliers : Fin 5 → Fin 7 → Fin 15 := ![![1, 9, 10, 11, 6, 7, 8], ![6, 5, 2, 12, 13, 10, 11], ![7, 6, 10, 9, 3, 14, 13], ![8, 7, 11, 10, 13, 12, 4], ![11, 13, 14, 4, 5, 6, 7]]

def correction (i : Fin 5) : Poly K 5 :=
  ∑ j : Fin 7,
    quadratic (Fin.castLE (by decide : 5 ≤ 15) (correctionGenerators i j)) *
      quadratic (correctionMultipliers i j)

def residual : Fin 5 → Poly K 5 :=
  ![squarefree 2 + squarefree 3 + squarefree 4,
    squarefree 0 + squarefree 3 + squarefree 4,
    squarefree 0 + squarefree 1 + squarefree 4,
    squarefree 0 + squarefree 1 + squarefree 2,
    squarefree 1 + squarefree 2 + squarefree 3]

set_option maxHeartbeats 4000000 in
theorem cycle_decomposition (i : Fin 5) :
    mixed (K := K) * quadratic (cycleEdges i) = residual i + correction i := by
  fin_cases i <;>
    simp [mixed, quadratic, squarefree, residual, correction, cycleEdges,
      correctionGenerators, correctionMultipliers, quadraticExponents,
      squarefreeExponents, exponent, Fin.sum_univ_succ,
      monomial_add_single, monomial_single_add, ← X_pow_eq_monomial] <;> ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- The displayed determinant is the actual coefficient minor of the five
cycle-edge products on the five squarefree quartics. -/
theorem cycle_projection (i j : Fin 5) :
    (mixed (K := K) * quadratic (cycleEdges i)).coeff (squarefreeExponents j) =
      (residualMatrix i j : K) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [mixed, quadratic, cycleEdges, squarefreeExponents, quadraticExponents,
      exponent, residualMatrix, Fin.sum_univ_succ, add_mul,
      monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff, Fin.forall_fin_succ]

theorem correction_mem (i : Fin 5) :
    correction (K := K) i ∈ generatorSpace * Forms K 5 2 := by
  apply Submodule.sum_mem
  intro j _
  exact Submodule.mul_mem_mul (square_mem_generatorSpace _) (quadratic_homogeneous _)

theorem residual_mem (i : Fin 5) :
    residual (K := K) i ∈ generatorSpace * Forms K 5 2 := by
  have hp : mixed (K := K) * quadratic (cycleEdges i) ∈ generatorSpace * Forms K 5 2 :=
    Submodule.mul_mem_mul mixed_mem_generatorSpace (quadratic_homogeneous (cycleEdges i))
  have h := (generatorSpace (K := K) * Forms K 5 2).sub_mem hp (correction_mem i)
  rwa [cycle_decomposition, add_sub_cancel_right] at h

def inverseCoefficients : Fin 5 → Fin 5 → ℤ :=
  ![![-1, 2, -1, 2, -1], ![-1, -1, 2, -1, 2], ![2, -1, -1, 2, -1],
    ![-1, 2, -1, -1, 2], ![2, -1, 2, -1, -1]]

theorem residual_inverse (i : Fin 5) :
    (3 : K) • squarefree (K := K) i =
      ∑ j : Fin 5, (inverseCoefficients i j : K) • residual j := by
  fin_cases i <;> simp [inverseCoefficients, residual, Fin.sum_univ_succ] <;> module

variable [CharZero K]

theorem squarefree_mem (i : Fin 5) :
    squarefree (K := K) i ∈ generatorSpace * Forms K 5 2 := by
  have h : (3 : K) • squarefree (K := K) i ∈ generatorSpace * Forms K 5 2 := by
    rw [residual_inverse]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (residual_mem j)
  have h' := (generatorSpace (K := K) * Forms K 5 2).smul_mem (3 : K)⁻¹ h
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (3 : K) ≠ 0), one_smul] using h'


/-- A list of all seventy degree-four exponents, with the five squarefree
ones placed after the sixty-five multiples of coordinate squares. -/
def quarticExponents (i : Fin 70) : Fin 5 →₀ ℕ :=
  if hi : i.val < 65 then squareProductExponents ⟨i.val, hi⟩
  else squarefreeExponents ⟨i.val - 65, by omega⟩

theorem quarticExponents_degree (i : Fin 70) : (quarticExponents i).degree = 4 := by
  unfold quarticExponents
  split_ifs
  · exact squareProductExponents_degree _
  · exact squarefreeExponents_degree _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem quarticExponents_injective : Function.Injective quarticExponents := by
  have heq : (fun i => encode (quarticExponents i)) = ![4, 12, 52, 252, 1252, 8, 28, 128, 628, 32, 132, 632, 152, 652, 752, 20, 60, 260, 1260, 16, 36, 136, 636, 40, 140, 640, 160, 660, 760, 100, 300, 1300, 56, 76, 176, 676, 80, 180, 680, 200, 700, 800, 500, 1500, 256, 276, 376, 876, 280, 380, 880, 400, 900, 1000, 2500, 1256, 1276, 1376, 1876, 1280, 1380, 1880, 1400, 1900, 2000, 780, 776, 756, 656, 156] := by
    funext i
    fin_cases i <;> norm_num [encode, quarticExponents, squareProductExponents,
      productGenerators, productMultipliers, quadraticExponents, squarefreeExponents, exponent]
  have h : Function.Injective (fun i => encode (quarticExponents i)) := by
    rw [heq]; decide +kernel
  intro i j hij
  exact h (congrArg encode hij)

omit [CharZero K] in
theorem squareProduct_mem (i : Fin 65) :
    monomial (squareProductExponents i) (1 : K) ∈ generatorSpace * Forms K 5 2 := by
  have h := Submodule.mul_mem_mul (square_mem_generatorSpace (K := K) (productGenerators i))
    (show quadratic (K := K) (productMultipliers i) ∈ Forms K 5 2 from quadratic_homogeneous _)
  simpa only [quadratic, squareProductExponents, monomial_mul_monomial, mul_one] using h

theorem quarticMonomial_mem (i : Fin 70) :
    monomial (quarticExponents i) (1 : K) ∈ generatorSpace * Forms K 5 2 := by
  unfold quarticExponents
  split_ifs
  · exact squareProduct_mem _
  · exact squarefree_mem _

/-- The sixty-five square multiples and the five recovered squarefree quartics
span the actual entire degree-four polynomial space. -/
theorem six_generators_surjective :
    Function.Surjective (quadraticMultiplication (generators (K := K))) := by
  let v : Fin 70 → Forms K 5 4 := fun i =>
    ⟨monomial (quarticExponents i) 1, isHomogeneous_monomial 1 (quarticExponents_degree i)⟩
  have hlin : LinearIndependent K v := by
    apply LinearIndependent.of_comp (Forms K 5 4).subtype
    exact (basisMonomials (Fin 5) K).linearIndependent.comp quarticExponents quarticExponents_injective
  have hle : Submodule.span K (Set.range v) ≤ quarticProducts K 5 generatorSpace := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact quarticMonomial_mem i
  have hlower := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hlin, Fintype.card_fin] at hlower
  have hupper := Submodule.finrank_le (quarticProducts K 5 (generatorSpace (K := K)))
  rw [← LinearMap.range_eq_top, range_quadraticMultiplication]
  change quarticProducts K 5 generatorSpace = ⊤
  apply Submodule.eq_top_of_finrank_eq
  norm_num [finrank_quartics, Nat.choose] at hupper ⊢
  omega

/-- Six explicit independent quadrics generate every quartic. -/
theorem witness_six_generators : QuarticWitness K 5 6 :=
  EndpointReduction.surjective_implies_witness
    ⟨generators, generators_independent, six_generators_surjective⟩

/-- The generic theorem for every admissible generator count in five variables,
over any characteristic-zero field. -/
theorem generic_five_variables (r : ℕ) (hr : r ≤ (5 + 1).choose 2) :
    GenericQuartic K 5 r := by
  exact EndpointReduction.adjacent_endpoints_imply_generic 5 6 (by decide)
    witness_five_squares witness_six_generators
    (by norm_num [Counts.chi, Counts.b2, Counts.b4, Nat.choose])
    (by norm_num [Counts.chi, Counts.b2, Counts.b4, Nat.choose]) hr

theorem witness_five_variables (r : ℕ) (hr : r ≤ (5 + 1).choose 2) :
    QuarticWitness K 5 r := genericQuartic_iff_witness.mp (generic_five_variables r hr)

/-- Complete generic quartic multiplication for one through five variables. -/
theorem generic_at_most_five (n r : ℕ) (hn : 1 ≤ n) (hn5 : n ≤ 5)
    (hr : r ≤ (n + 1).choose 2) : GenericQuartic K n r := by
  by_cases hn4 : n ≤ 4
  · exact FourVariables.generic_at_most_four n r hn hn4 hr
  · have hn5' : n = 5 := by omega
    subst n
    exact generic_five_variables r hr

end Quartic.FiveVariables
