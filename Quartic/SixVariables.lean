import Quartic.FiveVariables

/-!
# Complete six-variable endpoint witnesses

Six coordinate squares yield 111 independent quartics. On the fifteen
remaining squarefree quartics, multiplication by the sum of the fifteen mixed
quadrics is the disjoint-pair matrix. Its explicit inverse after multiplication
by six recovers every remaining quartic in characteristic zero.
-/

noncomputable section

namespace Quartic.SixVariables

open MvPolynomial Module SmallCases

variable {K : Type*} [Field K]

def exponent (a b c d e f : ℕ) : Fin 6 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c +
    Finsupp.single 3 d + Finsupp.single 4 e + Finsupp.single 5 f

def quadraticExponents : Fin 21 → (Fin 6 →₀ ℕ) := ![exponent 2 0 0 0 0 0, exponent 0 2 0 0 0 0, exponent 0 0 2 0 0 0, exponent 0 0 0 2 0 0, exponent 0 0 0 0 2 0, exponent 0 0 0 0 0 2, exponent 1 1 0 0 0 0, exponent 1 0 1 0 0 0, exponent 1 0 0 1 0 0, exponent 1 0 0 0 1 0, exponent 1 0 0 0 0 1, exponent 0 1 1 0 0 0, exponent 0 1 0 1 0 0, exponent 0 1 0 0 1 0, exponent 0 1 0 0 0 1, exponent 0 0 1 1 0 0, exponent 0 0 1 0 1 0, exponent 0 0 1 0 0 1, exponent 0 0 0 1 1 0, exponent 0 0 0 1 0 1, exponent 0 0 0 0 1 1]

theorem quadraticExponents_degree (i : Fin 21) : (quadraticExponents i).degree = 2 := by
  fin_cases i <;> simp [quadraticExponents, exponent]

def encode (e : Fin 6 →₀ ℕ) : ℕ :=
  e 0 + 5 * e 1 + 25 * e 2 + 125 * e 3 + 625 * e 4 + 3125 * e 5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem quadraticExponents_injective : Function.Injective quadraticExponents := by
  have heq : (fun i => encode (quadraticExponents i)) = ![2, 10, 50, 250, 1250, 6250, 6, 26, 126, 626, 3126, 30, 130, 630, 3130, 150, 650, 3150, 750, 3250, 3750] := by
    funext i
    fin_cases i <;> norm_num [encode, quadraticExponents, exponent]
  have h : Function.Injective (fun i => encode (quadraticExponents i)) := by
    rw [heq]; decide +kernel
  intro i j hij
  exact h (congrArg encode hij)

def productGenerators : Fin 111 → Fin 6 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]
def productMultipliers : Fin 111 → Fin 21 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
def squareProductExponents (i : Fin 111) : Fin 6 →₀ ℕ :=
  quadraticExponents (Fin.castLE (by decide : 6 ≤ 21) (productGenerators i)) +
    quadraticExponents (productMultipliers i)

theorem squareProductExponents_degree (i : Fin 111) : (squareProductExponents i).degree = 4 := by
  simp [squareProductExponents, quadraticExponents_degree]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem squareProductExponents_injective : Function.Injective squareProductExponents := by
  have heq : (fun i => encode (squareProductExponents i)) = ![4, 12, 52, 252, 1252, 6252, 8, 28, 128, 628, 3128, 32, 132, 632, 3132, 152, 652, 3152, 752, 3252, 3752, 20, 60, 260, 1260, 6260, 16, 36, 136, 636, 3136, 40, 140, 640, 3140, 160, 660, 3160, 760, 3260, 3760, 100, 300, 1300, 6300, 56, 76, 176, 676, 3176, 80, 180, 680, 3180, 200, 700, 3200, 800, 3300, 3800, 500, 1500, 6500, 256, 276, 376, 876, 3376, 280, 380, 880, 3380, 400, 900, 3400, 1000, 3500, 4000, 2500, 7500, 1256, 1276, 1376, 1876, 4376, 1280, 1380, 1880, 4380, 1400, 1900, 4400, 2000, 4500, 5000, 12500, 6256, 6276, 6376, 6876, 9376, 6280, 6380, 6880, 9380, 6400, 6900, 9400, 7000, 9500, 10000] := by
    funext i
    fin_cases i <;> norm_num [encode, squareProductExponents, productGenerators,
      productMultipliers, quadraticExponents, exponent]
  have h : Function.Injective (fun i => encode (squareProductExponents i)) := by
    rw [heq]; decide +kernel
  intro i j hij
  exact h (congrArg encode hij)

/-- Six squares attain the expected fifteen-dimensional quartic quotient. -/
theorem witness_six_squares : QuarticWitness K 6 6 := by
  exact witness_of_monomial_products
    (q := quadraticExponents ∘ Fin.castLE (by decide : 6 ≤ 21))
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

/-- A squarefree quartic is indexed by the complementary pair of variables. -/
def squarefreeExponents : Fin 15 → (Fin 6 →₀ ℕ) := ![exponent 0 0 1 1 1 1, exponent 0 1 0 1 1 1, exponent 0 1 1 0 1 1, exponent 0 1 1 1 0 1, exponent 0 1 1 1 1 0, exponent 1 0 0 1 1 1, exponent 1 0 1 0 1 1, exponent 1 0 1 1 0 1, exponent 1 0 1 1 1 0, exponent 1 1 0 0 1 1, exponent 1 1 0 1 0 1, exponent 1 1 0 1 1 0, exponent 1 1 1 0 0 1, exponent 1 1 1 0 1 0, exponent 1 1 1 1 0 0]

theorem squarefreeExponents_degree (i : Fin 15) : (squarefreeExponents i).degree = 4 := by
  fin_cases i <;> simp [squarefreeExponents, exponent]

def quadratic (i : Fin 21) : Poly K 6 := monomial (quadraticExponents i) 1
def mixed : Poly K 6 := ∑ i : Fin 15, quadratic ⟨i.val + 6, by omega⟩
def squarefree (i : Fin 15) : Poly K 6 := monomial (squarefreeExponents i) 1

def generatorPolys : Fin 7 → Poly K 6 :=
  ![quadratic 0, quadratic 1, quadratic 2, quadratic 3, quadratic 4, quadratic 5, mixed]

theorem quadratic_homogeneous (i : Fin 21) : IsHomogeneous (quadratic (K := K) i) 2 :=
  isHomogeneous_monomial 1 (quadraticExponents_degree i)

theorem mixed_homogeneous : IsHomogeneous (mixed (K := K)) 2 := by
  exact (Forms K 6 2).sum_mem fun i _ => quadratic_homogeneous _

def generators (i : Fin 7) : Forms K 6 2 :=
  ⟨generatorPolys i, by
    fin_cases i <;> first | exact quadratic_homogeneous _ | exact mixed_homogeneous⟩

def separatingExponents : Fin 7 → (Fin 6 →₀ ℕ) :=
  ![quadraticExponents 0, quadraticExponents 1, quadraticExponents 2,
    quadraticExponents 3, quadraticExponents 4, quadraticExponents 5, quadraticExponents 6]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem separating_coefficients (i j : Fin 7) :
    (generatorPolys (K := K) j).coeff (separatingExponents i) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [generatorPolys, separatingExponents, mixed, quadratic,
      quadraticExponents, exponent, Fin.sum_univ_succ, coeff_monomial,
      Finsupp.ext_iff, Fin.forall_fin_succ]

theorem generators_independent : LinearIndependent K (generators (K := K)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h := congrArg (fun p : Forms K 6 2 => p.val.coeff (separatingExponents i)) hc
  simpa [Submodule.coe_sum, Submodule.coe_smul, coeff_sum, coeff_smul,
    generators, separating_coefficients, Submodule.coe_zero, AddMonoidAlgebra.coeff_zero,
    Pi.zero_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] using h

def generatorSpace : Submodule K (Poly K 6) :=
  Submodule.span K (Set.range (generatorPolys (K := K)))

theorem square_mem_generatorSpace (i : Fin 6) :
    quadratic (K := K) (Fin.castLE (by decide : 6 ≤ 21) i) ∈ generatorSpace := by
  have h : quadratic (K := K) (Fin.castLE (by decide : 6 ≤ 21) i) =
      generatorPolys (Fin.castLE (by decide : 6 ≤ 7) i) := by fin_cases i <;> rfl
  rw [h]
  exact Submodule.subset_span ⟨_, rfl⟩

theorem mixed_mem_generatorSpace : mixed (K := K) ∈ generatorSpace :=
  Submodule.subset_span ⟨6, rfl⟩

def edges : Fin 15 → Fin 21 := fun i => ⟨i.val + 6, by omega⟩

def correctionGenerators : Fin 15 → Fin 9 → Fin 6 := ![![0, 0, 0, 0, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 2, 2, 2, 2], ![0, 0, 0, 0, 0, 3, 3, 3, 3], ![0, 0, 0, 0, 0, 4, 4, 4, 4], ![0, 0, 0, 0, 0, 5, 5, 5, 5], ![1, 2, 1, 1, 1, 1, 2, 2, 2], ![1, 3, 1, 1, 1, 1, 3, 3, 3], ![1, 4, 1, 1, 1, 1, 4, 4, 4], ![1, 5, 1, 1, 1, 1, 5, 5, 5], ![2, 3, 2, 3, 2, 2, 2, 3, 3], ![2, 4, 2, 4, 2, 2, 2, 4, 4], ![2, 5, 2, 5, 2, 2, 2, 5, 5], ![3, 4, 3, 4, 3, 4, 3, 3, 4], ![3, 5, 3, 5, 3, 5, 3, 3, 5], ![4, 5, 4, 5, 4, 5, 4, 5, 4]]
def correctionMultipliers : Fin 15 → Fin 9 → Fin 21 := ![![1, 11, 12, 13, 14, 7, 8, 9, 10], ![11, 2, 15, 16, 17, 6, 8, 9, 10], ![12, 15, 3, 18, 19, 6, 7, 9, 10], ![13, 16, 18, 4, 20, 6, 7, 8, 10], ![14, 17, 19, 20, 5, 6, 7, 8, 9], ![7, 6, 2, 15, 16, 17, 12, 13, 14], ![8, 6, 15, 3, 18, 19, 11, 13, 14], ![9, 6, 16, 18, 4, 20, 11, 12, 14], ![10, 6, 17, 19, 20, 5, 11, 12, 13], ![8, 7, 12, 11, 3, 18, 19, 16, 17], ![9, 7, 13, 11, 18, 4, 20, 15, 17], ![10, 7, 14, 11, 19, 20, 5, 15, 16], ![9, 8, 13, 12, 16, 15, 4, 20, 19], ![10, 8, 14, 12, 17, 15, 20, 5, 18], ![10, 9, 14, 13, 17, 16, 19, 18, 5]]

def correction (i : Fin 15) : Poly K 6 :=
  ∑ j : Fin 9,
    quadratic (Fin.castLE (by decide : 6 ≤ 21) (correctionGenerators i j)) *
      quadratic (correctionMultipliers i j)

/-- The six squarefree terms disjoint from the multiplier pair. -/
def residual : Fin 15 → Poly K 6 := ![squarefree 9 + squarefree 10 + squarefree 11 + squarefree 12 + squarefree 13 + squarefree 14, squarefree 6 + squarefree 7 + squarefree 8 + squarefree 12 + squarefree 13 + squarefree 14, squarefree 5 + squarefree 7 + squarefree 8 + squarefree 10 + squarefree 11 + squarefree 14, squarefree 5 + squarefree 6 + squarefree 8 + squarefree 9 + squarefree 11 + squarefree 13, squarefree 5 + squarefree 6 + squarefree 7 + squarefree 9 + squarefree 10 + squarefree 12, squarefree 2 + squarefree 3 + squarefree 4 + squarefree 12 + squarefree 13 + squarefree 14, squarefree 1 + squarefree 3 + squarefree 4 + squarefree 10 + squarefree 11 + squarefree 14, squarefree 1 + squarefree 2 + squarefree 4 + squarefree 9 + squarefree 11 + squarefree 13, squarefree 1 + squarefree 2 + squarefree 3 + squarefree 9 + squarefree 10 + squarefree 12, squarefree 0 + squarefree 3 + squarefree 4 + squarefree 7 + squarefree 8 + squarefree 14, squarefree 0 + squarefree 2 + squarefree 4 + squarefree 6 + squarefree 8 + squarefree 13, squarefree 0 + squarefree 2 + squarefree 3 + squarefree 6 + squarefree 7 + squarefree 12, squarefree 0 + squarefree 1 + squarefree 4 + squarefree 5 + squarefree 8 + squarefree 11, squarefree 0 + squarefree 1 + squarefree 3 + squarefree 5 + squarefree 7 + squarefree 10, squarefree 0 + squarefree 1 + squarefree 2 + squarefree 5 + squarefree 6 + squarefree 9]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem product_decomposition (i : Fin 15) :
    mixed (K := K) * quadratic (edges i) = residual i + correction i := by
  fin_cases i <;>
    simp [mixed, quadratic, squarefree, residual, correction, edges,
      correctionGenerators, correctionMultipliers, quadraticExponents,
      squarefreeExponents, exponent, Fin.sum_univ_succ,
      monomial_add_single, monomial_single_add, ← X_pow_eq_monomial] <;> ring

theorem correction_mem (i : Fin 15) :
    correction (K := K) i ∈ generatorSpace * Forms K 6 2 := by
  apply Submodule.sum_mem
  intro j _
  exact Submodule.mul_mem_mul (square_mem_generatorSpace _) (quadratic_homogeneous _)

theorem residual_mem (i : Fin 15) :
    residual (K := K) i ∈ generatorSpace * Forms K 6 2 := by
  have hp : mixed (K := K) * quadratic (edges i) ∈ generatorSpace * Forms K 6 2 :=
    Submodule.mul_mem_mul mixed_mem_generatorSpace (quadratic_homogeneous (edges i))
  have h := (generatorSpace (K := K) * Forms K 6 2).sub_mem hp (correction_mem i)
  rwa [product_decomposition, add_sub_cancel_right] at h

/-- Six times the inverse disjoint-pair matrix: three on the diagonal, one for
disjoint pairs, and minus one for distinct intersecting pairs. -/
def inverseCoefficients : Fin 15 → Fin 15 → ℤ := ![![3, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1], ![-1, 3, -1, -1, -1, -1, 1, 1, 1, -1, -1, -1, 1, 1, 1], ![-1, -1, 3, -1, -1, 1, -1, 1, 1, -1, 1, 1, -1, -1, 1], ![-1, -1, -1, 3, -1, 1, 1, -1, 1, 1, -1, 1, -1, 1, -1], ![-1, -1, -1, -1, 3, 1, 1, 1, -1, 1, 1, -1, 1, -1, -1], ![-1, -1, 1, 1, 1, 3, -1, -1, -1, -1, -1, -1, 1, 1, 1], ![-1, 1, -1, 1, 1, -1, 3, -1, -1, -1, 1, 1, -1, -1, 1], ![-1, 1, 1, -1, 1, -1, -1, 3, -1, 1, -1, 1, -1, 1, -1], ![-1, 1, 1, 1, -1, -1, -1, -1, 3, 1, 1, -1, 1, -1, -1], ![1, -1, -1, 1, 1, -1, -1, 1, 1, 3, -1, -1, -1, -1, 1], ![1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 3, -1, -1, 1, -1], ![1, -1, 1, 1, -1, -1, 1, 1, -1, -1, -1, 3, 1, -1, -1], ![1, 1, -1, -1, 1, 1, -1, -1, 1, -1, -1, 1, 3, -1, -1], ![1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, -1, 3, -1], ![1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, -1, -1, -1, 3]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem residual_inverse (i : Fin 15) :
    (6 : K) • squarefree (K := K) i =
      ∑ j : Fin 15, (inverseCoefficients i j : K) • residual j := by
  fin_cases i <;> simp [inverseCoefficients, residual, Fin.sum_univ_succ] <;> module

variable [CharZero K]

theorem squarefree_mem (i : Fin 15) :
    squarefree (K := K) i ∈ generatorSpace * Forms K 6 2 := by
  have h : (6 : K) • squarefree (K := K) i ∈ generatorSpace * Forms K 6 2 := by
    rw [residual_inverse]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (residual_mem j)
  have h' := (generatorSpace (K := K) * Forms K 6 2).smul_mem (6 : K)⁻¹ h
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (6 : K) ≠ 0), one_smul] using h'

/-- The 111 square multiples followed by all fifteen squarefree exponents. -/
def quarticExponents (i : Fin 126) : Fin 6 →₀ ℕ :=
  if hi : i.val < 111 then squareProductExponents ⟨i.val, hi⟩
  else squarefreeExponents ⟨i.val - 111, by omega⟩

theorem quarticExponents_degree (i : Fin 126) : (quarticExponents i).degree = 4 := by
  unfold quarticExponents
  split_ifs
  · exact squareProductExponents_degree _
  · exact squarefreeExponents_degree _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem quarticExponents_injective : Function.Injective quarticExponents := by
  have heq : (fun i => encode (quarticExponents i)) = ![4, 12, 52, 252, 1252, 6252, 8, 28, 128, 628, 3128, 32, 132, 632, 3132, 152, 652, 3152, 752, 3252, 3752, 20, 60, 260, 1260, 6260, 16, 36, 136, 636, 3136, 40, 140, 640, 3140, 160, 660, 3160, 760, 3260, 3760, 100, 300, 1300, 6300, 56, 76, 176, 676, 3176, 80, 180, 680, 3180, 200, 700, 3200, 800, 3300, 3800, 500, 1500, 6500, 256, 276, 376, 876, 3376, 280, 380, 880, 3380, 400, 900, 3400, 1000, 3500, 4000, 2500, 7500, 1256, 1276, 1376, 1876, 4376, 1280, 1380, 1880, 4380, 1400, 1900, 4400, 2000, 4500, 5000, 12500, 6256, 6276, 6376, 6876, 9376, 6280, 6380, 6880, 9380, 6400, 6900, 9400, 7000, 9500, 10000, 3900, 3880, 3780, 3280, 780, 3876, 3776, 3276, 776, 3756, 3256, 756, 3156, 656, 156] := by
    funext i
    fin_cases i <;> norm_num [encode, quarticExponents, squareProductExponents,
      productGenerators, productMultipliers, quadraticExponents, squarefreeExponents, exponent]
  have h : Function.Injective (fun i => encode (quarticExponents i)) := by
    rw [heq]; decide +kernel
  intro i j hij
  exact h (congrArg encode hij)

omit [CharZero K] in
theorem squareProduct_mem (i : Fin 111) :
    monomial (squareProductExponents i) (1 : K) ∈ generatorSpace * Forms K 6 2 := by
  have h := Submodule.mul_mem_mul (square_mem_generatorSpace (K := K) (productGenerators i))
    (show quadratic (K := K) (productMultipliers i) ∈ Forms K 6 2 from quadratic_homogeneous _)
  simpa only [quadratic, squareProductExponents, monomial_mul_monomial, mul_one] using h

theorem quarticMonomial_mem (i : Fin 126) :
    monomial (quarticExponents i) (1 : K) ∈ generatorSpace * Forms K 6 2 := by
  unfold quarticExponents
  split_ifs
  · exact squareProduct_mem _
  · exact squarefree_mem _

/-- Seven concrete independent quadrics generate all 126 quartics. -/
theorem seven_generators_surjective :
    Function.Surjective (quadraticMultiplication (generators (K := K))) := by
  let v : Fin 126 → Forms K 6 4 := fun i =>
    ⟨monomial (quarticExponents i) 1, isHomogeneous_monomial 1 (quarticExponents_degree i)⟩
  have hlin : LinearIndependent K v := by
    apply LinearIndependent.of_comp (Forms K 6 4).subtype
    exact (basisMonomials (Fin 6) K).linearIndependent.comp quarticExponents quarticExponents_injective
  have hle : Submodule.span K (Set.range v) ≤ quarticProducts K 6 generatorSpace := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact quarticMonomial_mem i
  have hlower := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hlin, Fintype.card_fin] at hlower
  have hupper := Submodule.finrank_le (quarticProducts K 6 (generatorSpace (K := K)))
  rw [← LinearMap.range_eq_top, range_quadraticMultiplication]
  change quarticProducts K 6 generatorSpace = ⊤
  apply Submodule.eq_top_of_finrank_eq
  norm_num [finrank_quartics, Nat.choose] at hupper ⊢
  omega

theorem witness_seven_generators : QuarticWitness K 6 7 :=
  EndpointReduction.surjective_implies_witness
    ⟨generators, generators_independent, seven_generators_surjective⟩

/-- Every admissible count in six variables has the expected generic quartic
dimension over any characteristic-zero field. -/
theorem generic_six_variables (r : ℕ) (hr : r ≤ (6 + 1).choose 2) :
    GenericQuartic K 6 r := by
  exact EndpointReduction.adjacent_endpoints_imply_generic 6 7 (by decide)
    witness_six_squares witness_seven_generators
    (by norm_num [Counts.chi, Counts.b2, Counts.b4, Nat.choose])
    (by norm_num [Counts.chi, Counts.b2, Counts.b4, Nat.choose]) hr

theorem witness_six_variables (r : ℕ) (hr : r ≤ (6 + 1).choose 2) :
    QuarticWitness K 6 r := genericQuartic_iff_witness.mp (generic_six_variables r hr)

/-- Complete generic quartic multiplication for one through six variables. -/
theorem generic_at_most_six (n r : ℕ) (hn : 1 ≤ n) (hn6 : n ≤ 6)
    (hr : r ≤ (n + 1).choose 2) : GenericQuartic K n r := by
  by_cases hn5 : n ≤ 5
  · exact FiveVariables.generic_at_most_five n r hn hn5 hr
  · have hn6' : n = 6 := by omega
    subst n
    exact generic_six_variables r hr

end Quartic.SixVariables
