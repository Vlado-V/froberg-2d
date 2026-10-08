import Quartic.Multiplication
import Quartic.StandardCases
import Quartic.RankOpen

/-!
# Complete monomial witnesses in two and three variables

Explicit distinct quartic monomials certify the multiplication rank. The
universal Koszul lower bound then determines the quotient dimension exactly.
-/

noncomputable section

namespace Quartic.SmallCases

open MvPolynomial Module

variable {K : Type*} [Field K] {n r k : ℕ}

/-- A finite list of distinct monomial products certifies an actual witness. -/
theorem witness_of_monomial_products
    (q : Fin r → (Fin n →₀ ℕ))
    (hq : ∀ i, (q i).degree = 2) (hiq : Function.Injective q)
    (e : Fin k → (Fin n →₀ ℕ))
    (he : ∀ i, (e i).degree = 4) (hie : Function.Injective e)
    (generator : Fin k → Fin r) (multiplier : Fin k → (Fin n →₀ ℕ))
    (hm : ∀ i, (multiplier i).degree = 2)
    (hproduct : ∀ i, q (generator i) + multiplier i = e i)
    (hsize : (n + 3).choose 4 ≤ k + expectedDimension n r) :
    QuarticWitness K n r := by
  let Q : Submodule K (Poly K n) :=
    Submodule.span K (Set.range (fun i => monomial (q i) (1 : K)))
  have hQ : Q ≤ Forms K n 2 := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact isHomogeneous_monomial 1 (hq i)
  have hlinq : LinearIndependent K (fun i => monomial (q i) (1 : K)) := by
    exact (basisMonomials (Fin n) K).linearIndependent.comp q hiq
  have hdimQ : finrank K Q = r := by
    dsimp only [Q]
    rw [finrank_span_eq_card hlinq, Fintype.card_fin]
  let v : Fin k → Forms K n 4 := fun i =>
    ⟨monomial (e i) 1, isHomogeneous_monomial 1 (he i)⟩
  have hlinv : LinearIndependent K v := by
    apply LinearIndependent.of_comp (Forms K n 4).subtype
    exact (basisMonomials (Fin n) K).linearIndependent.comp e hie
  have hv : Submodule.span K (Set.range v) ≤ quarticProducts K n Q := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change monomial (e i) (1 : K) ∈ Q * Forms K n 2
    have h := Submodule.mul_mem_mul
      (show monomial (q (generator i)) (1 : K) ∈ Q from Submodule.subset_span ⟨generator i, rfl⟩)
      (show monomial (multiplier i) (1 : K) ∈ Forms K n 2 from
        isHomogeneous_monomial 1 (hm i))
    simpa only [monomial_mul_monomial, mul_one, hproduct] using h
  have hrank := Submodule.finrank_mono hv
  rw [finrank_span_eq_card hlinv, Fintype.card_fin] at hrank
  have hquot := (quarticProducts K n Q).finrank_quotient_add_finrank
  rw [finrank_quartics] at hquot
  have hlower := quadratic_subspace_quotient_lower_bound Q hQ
  rw [hdimQ] at hlower
  change expectedDimension n r ≤ finrank K ((Forms K n 4) ⧸ quarticProducts K n Q) at hlower
  refine ⟨Q, hQ, hdimQ, ?_⟩
  change finrank K ((Forms K n 4) ⧸ quarticProducts K n Q) = expectedDimension n r
  omega

def exponent2 (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b

def quadraticExponents2 : Fin 3 → (Fin 2 →₀ ℕ) :=
  ![exponent2 2 0, exponent2 0 2, exponent2 1 1]

theorem quadraticExponents2_degree (i : Fin 3) : (quadraticExponents2 i).degree = 2 := by
  fin_cases i <;> simp [quadraticExponents2, exponent2]

theorem quadraticExponents2_injective : Function.Injective quadraticExponents2 := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [quadraticExponents2, exponent2, Finsupp.ext_iff, Fin.forall_fin_succ]

def productGenerators2 : Fin 5 → Fin 2 := ![0, 0, 0, 1, 1]
def productMultipliers2 : Fin 5 → Fin 3 := ![0, 2, 1, 2, 1]
def quarticExponents2 (i : Fin 5) : Fin 2 →₀ ℕ :=
  quadraticExponents2 (Fin.castLE (by decide : 2 ≤ 3) (productGenerators2 i)) +
    quadraticExponents2 (productMultipliers2 i)

theorem quarticExponents2_degree (i : Fin 5) : (quarticExponents2 i).degree = 4 := by
  simp [quarticExponents2, quadraticExponents2_degree]

theorem quarticExponents2_injective : Function.Injective quarticExponents2 := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [quarticExponents2, productGenerators2, productMultipliers2,
      quadraticExponents2, exponent2, Finsupp.ext_iff, Fin.forall_fin_succ]

/-- Any prefix containing `x²,y²` has zero quartic quotient in two variables. -/
theorem witness_two_variables_large (r : ℕ) (hr2 : 2 ≤ r) (hr3 : r ≤ 3) :
    QuarticWitness K 2 r := by
  apply witness_of_monomial_products
    (q := quadraticExponents2 ∘ Fin.castLE hr3)
    (e := quarticExponents2)
    (generator := Fin.castLE hr2 ∘ productGenerators2)
    (multiplier := quadraticExponents2 ∘ productMultipliers2)
  · intro i; exact quadraticExponents2_degree _
  · exact quadraticExponents2_injective.comp (Fin.castLE_injective _)
  · exact quarticExponents2_degree
  · exact quarticExponents2_injective
  · intro i; exact quadraticExponents2_degree _
  · intro i; rfl
  · interval_cases r <;> norm_num [expectedDimension, Nat.choose]

def exponent3 (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c

def quadraticExponents3 : Fin 6 → (Fin 3 →₀ ℕ) :=
  ![exponent3 2 0 0, exponent3 0 2 0, exponent3 0 0 2,
    exponent3 1 1 0, exponent3 1 0 1, exponent3 0 1 1]

theorem quadraticExponents3_degree (i : Fin 6) : (quadraticExponents3 i).degree = 2 := by
  fin_cases i <;> simp [quadraticExponents3, exponent3]

theorem quadraticExponents3_injective : Function.Injective quadraticExponents3 := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [quadraticExponents3, exponent3, Finsupp.ext_iff, Fin.forall_fin_succ]

def productGenerators3 : Fin 15 → Fin 3 := ![0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 1, 1, 1, 2, 2]
def productMultipliers3 : Fin 15 → Fin 6 := ![0, 3, 4, 1, 5, 2, 3, 4, 3, 4, 1, 5, 2, 5, 2]
def quarticExponents3 (i : Fin 15) : Fin 3 →₀ ℕ :=
  quadraticExponents3 (Fin.castLE (by decide : 3 ≤ 6) (productGenerators3 i)) +
    quadraticExponents3 (productMultipliers3 i)

theorem quarticExponents3_degree (i : Fin 15) : (quarticExponents3 i).degree = 4 := by
  simp [quarticExponents3, quadraticExponents3_degree]

set_option maxHeartbeats 2000000 in
theorem quarticExponents3_injective : Function.Injective quarticExponents3 := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [quarticExponents3, productGenerators3, productMultipliers3,
      quadraticExponents3, exponent3, Finsupp.ext_iff, Fin.forall_fin_succ]

/-- Any prefix containing all three coordinate squares kills every quartic. -/
theorem witness_three_variables_large (r : ℕ) (hr3 : 3 ≤ r) (hr6 : r ≤ 6) :
    QuarticWitness K 3 r := by
  apply witness_of_monomial_products
    (q := quadraticExponents3 ∘ Fin.castLE hr6)
    (e := quarticExponents3)
    (generator := Fin.castLE hr3 ∘ productGenerators3)
    (multiplier := quadraticExponents3 ∘ productMultipliers3)
  · intro i; exact quadraticExponents3_degree _
  · exact quadraticExponents3_injective.comp (Fin.castLE_injective _)
  · exact quarticExponents3_degree
  · exact quarticExponents3_injective
  · intro i; exact quadraticExponents3_degree _
  · intro i; rfl
  · interval_cases r <;> norm_num [expectedDimension, Nat.choose]

def productGenerators3Two : Fin 11 → Fin 2 := ![0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1]
def productMultipliers3Two : Fin 11 → Fin 6 := ![0, 3, 4, 1, 5, 2, 3, 4, 1, 5, 2]
def quarticExponents3Two (i : Fin 11) : Fin 3 →₀ ℕ :=
  quadraticExponents3 (Fin.castLE (by decide : 2 ≤ 6) (productGenerators3Two i)) +
    quadraticExponents3 (productMultipliers3Two i)

theorem quarticExponents3Two_degree (i : Fin 11) : (quarticExponents3Two i).degree = 4 := by
  simp [quarticExponents3Two, quadraticExponents3_degree]

set_option maxHeartbeats 2000000 in
theorem quarticExponents3Two_injective : Function.Injective quarticExponents3Two := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [quarticExponents3Two, productGenerators3Two, productMultipliers3Two,
      quadraticExponents3, exponent3, Finsupp.ext_iff, Fin.forall_fin_succ]

/-- The two squares `x²,y²` have eleven independent quartic products in three variables. -/
theorem witness_three_variables_two : QuarticWitness K 3 2 := by
  apply witness_of_monomial_products
    (q := quadraticExponents3 ∘ Fin.castLE (by decide : 2 ≤ 6))
    (e := quarticExponents3Two)
    (generator := productGenerators3Two)
    (multiplier := quadraticExponents3 ∘ productMultipliers3Two)
  · intro i; exact quadraticExponents3_degree _
  · exact quadraticExponents3_injective.comp (Fin.castLE_injective _)
  · exact quarticExponents3Two_degree
  · exact quarticExponents3Two_injective
  · intro i; exact quadraticExponents3_degree _
  · intro i; rfl
  · norm_num [expectedDimension, Nat.choose]

/-- Every admissible count in two variables has an actual witness. -/
theorem witness_two_variables (r : ℕ) (hr : r ≤ (2 + 1).choose 2) :
    QuarticWitness K 2 r := by
  have hr3 : r ≤ 3 := by simpa using hr
  rcases lt_or_ge r 2 with hsmall | hlarge
  · interval_cases r
    · exact zero_generator_witness (K := K) (n := 2)
    · exact one_generator_witness (by decide)
  · exact witness_two_variables_large r hlarge hr3

/-- Every admissible count in three variables has an actual witness. -/
theorem witness_three_variables (r : ℕ) (hr : r ≤ (3 + 1).choose 2) :
    QuarticWitness K 3 r := by
  have hr6 : r ≤ 6 := by simpa [Nat.choose] using hr
  rcases lt_or_ge r 3 with hsmall | hlarge
  · interval_cases r
    · exact zero_generator_witness (K := K) (n := 3)
    · exact one_generator_witness (by decide)
    · exact witness_three_variables_two
  · exact witness_three_variables_large r hlarge hr6

/-- The generic quartic statement is proved for every admissible two-variable count. -/
theorem generic_two_variables (r : ℕ) (hr : r ≤ (2 + 1).choose 2) :
    GenericQuartic K 2 r :=
  witness_implies_generic (witness_two_variables r hr)

/-- The generic quartic statement is proved for every admissible three-variable count. -/
theorem generic_three_variables (r : ℕ) (hr : r ≤ (3 + 1).choose 2) :
    GenericQuartic K 3 r :=
  witness_implies_generic (witness_three_variables r hr)

/-- Complete generic theorem in at most three variables, for every possible generator count. -/
theorem generic_at_most_three (n r : ℕ) (hn : 1 ≤ n) (hn3 : n ≤ 3)
    (hr : r ≤ (n + 1).choose 2) : GenericQuartic K n r := by
  interval_cases n
  · exact generic_one_variable r hr
  · exact generic_two_variables r hr
  · exact generic_three_variables r hr

end Quartic.SmallCases
