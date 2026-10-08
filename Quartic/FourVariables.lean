import Quartic.SmallCases
import Quartic.EndpointReduction

/-!
# Complete monomial witnesses in four variables

The first four coordinate squares produce 34 distinct quartics, with only the
squarefree quartic missing. Adjoining `x₀x₁` supplies that last quartic. These
actual endpoint witnesses give every generator count by endpoint reduction.
-/

noncomputable section

namespace Quartic.FourVariables

open MvPolynomial Module SmallCases

variable {K : Type*} [Field K]

def exponent (a b c d : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c + Finsupp.single 3 d

def quadraticExponents : Fin 10 → (Fin 4 →₀ ℕ) :=
  ![exponent 2 0 0 0, exponent 0 2 0 0, exponent 0 0 2 0, exponent 0 0 0 2, exponent 1 1 0 0, exponent 1 0 1 0, exponent 1 0 0 1, exponent 0 1 1 0, exponent 0 1 0 1, exponent 0 0 1 1]

theorem quadraticExponents_degree (i : Fin 10) : (quadraticExponents i).degree = 2 := by
  fin_cases i <;> simp [quadraticExponents, exponent]

/-- Base-five coordinates distinguish all exponents used in this certificate. -/
def encode (e : Fin 4 →₀ ℕ) : ℕ := e 0 + 5 * e 1 + 25 * e 2 + 125 * e 3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem quadraticExponents_injective : Function.Injective quadraticExponents := by
  have heq : (fun i => encode (quadraticExponents i)) = ![2, 10, 50, 250, 6, 26, 126, 30, 130, 150] := by
    funext i
    fin_cases i <;> norm_num [encode, quadraticExponents, exponent]
  have h : Function.Injective (fun i => encode (quadraticExponents i)) := by
    rw [heq]
    decide +kernel
  intro i j hij
  exact h (congrArg encode hij)

def productGenerators : Fin 35 → Fin 5 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 4]
def productMultipliers : Fin 35 → Fin 10 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 2, 3, 4, 5, 6, 7, 8, 9, 3, 4, 5, 6, 7, 8, 9, 9]
def quarticExponents (i : Fin 35) : Fin 4 →₀ ℕ :=
  quadraticExponents (Fin.castLE (by decide : 5 ≤ 10) (productGenerators i)) +
    quadraticExponents (productMultipliers i)

theorem quarticExponents_degree (i : Fin 35) : (quarticExponents i).degree = 4 := by
  simp [quarticExponents, quadraticExponents_degree]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem quarticExponents_injective : Function.Injective quarticExponents := by
  have heq : (fun i => encode (quarticExponents i)) = ![4, 12, 52, 252, 8, 28, 128, 32, 132, 152, 20, 60, 260, 16, 36, 136, 40, 140, 160, 100, 300, 56, 76, 176, 80, 180, 200, 500, 256, 276, 376, 280, 380, 400, 156] := by
    funext i
    fin_cases i <;> norm_num [encode, quarticExponents, productGenerators,
      productMultipliers, quadraticExponents, exponent]
  have h : Function.Injective (fun i => encode (quarticExponents i)) := by
    rw [heq]
    decide +kernel
  intro i j hij
  exact h (congrArg encode hij)

def squareProductGenerator (i : Fin 34) : Fin 4 :=
  ⟨(productGenerators (Fin.castLE (by decide : 34 ≤ 35) i)).val,
    by fin_cases i <;> decide⟩

/-- Four coordinate squares attain the expected one-dimensional quartic quotient. -/
theorem witness_four_squares : QuarticWitness K 4 4 := by
  exact witness_of_monomial_products
    (q := quadraticExponents ∘ Fin.castLE (by decide : 4 ≤ 10))
    (e := quarticExponents ∘ Fin.castLE (by decide : 34 ≤ 35))
    (generator := squareProductGenerator)
    (multiplier := quadraticExponents ∘ productMultipliers ∘ Fin.castLE (by decide : 34 ≤ 35))
    (hq := fun i => quadraticExponents_degree _)
    (hiq := quadraticExponents_injective.comp (Fin.castLE_injective _))
    (he := fun i => quarticExponents_degree _)
    (hie := quarticExponents_injective.comp (Fin.castLE_injective _))
    (hm := fun i => quadraticExponents_degree _)
    (hproduct := fun i => rfl)
    (hsize := by norm_num [expectedDimension, Nat.choose])

/-- The coordinate squares and `x₀x₁` generate every quartic. -/
theorem witness_five_generators : QuarticWitness K 4 5 := by
  apply witness_of_monomial_products
    (q := quadraticExponents ∘ Fin.castLE (by decide : 5 ≤ 10))
    (e := quarticExponents)
    (generator := productGenerators)
    (multiplier := quadraticExponents ∘ productMultipliers)
  · intro i; exact quadraticExponents_degree _
  · exact quadraticExponents_injective.comp (Fin.castLE_injective _)
  · exact quarticExponents_degree
  · exact quarticExponents_injective
  · intro i; exact quadraticExponents_degree _
  · intro i; rfl
  · norm_num [expectedDimension, Nat.choose]

/-- Every admissible generator count in four variables satisfies the generic theorem. -/
theorem generic_four_variables (r : ℕ) (hr : r ≤ (4 + 1).choose 2) :
    GenericQuartic K 4 r := by
  exact EndpointReduction.adjacent_endpoints_imply_generic 4 5 (by decide)
    witness_four_squares witness_five_generators
    (by norm_num [Counts.chi, Counts.b2, Counts.b4, Nat.choose])
    (by norm_num [Counts.chi, Counts.b2, Counts.b4, Nat.choose]) hr

theorem witness_four_variables (r : ℕ) (hr : r ≤ (4 + 1).choose 2) :
    QuarticWitness K 4 r := genericQuartic_iff_witness.mp (generic_four_variables r hr)

/-- The complete generic theorem for one through four variables, over any field. -/
theorem generic_at_most_four (n r : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4)
    (hr : r ≤ (n + 1).choose 2) : GenericQuartic K n r := by
  by_cases hn3 : n ≤ 3
  · exact SmallCases.generic_at_most_three n r hn hn3 hr
  · have hn4' : n = 4 := by omega
    subst n
    exact generic_four_variables r hr

end Quartic.FourVariables
