import Quartic.Counts

/-!
# Logical reductions used by the manuscript

The transfer statement in this module is a hypothesis. This module proves the
induction logic and the elementary interpretation of an Euler difference; it
does not prove the geometric transfer or any generic-rank assertion.
-/

namespace Quartic.Induction

/-- Bases through 30 and the transfer from `m` to `m + 3` for `m ≥ 28`
cover every natural dimension. -/
theorem from_bases_and_three_step (P : ℕ → Prop)
    (hbase : ∀ n, n ≤ 30 → P n)
    (hstep : ∀ m, 28 ≤ m → P m → P (m + 3)) : ∀ n, P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 30
    · exact hbase n hn
    · have hm : 28 ≤ n - 3 := by omega
      have hlt : n - 3 < n := by omega
      have heq : n - 3 + 3 = n := by omega
      simpa only [heq] using hstep (n - 3) hm (ih (n - 3) hlt)

/-- Version restricted to positive dimensions, avoiding an artificial base at zero. -/
theorem from_positive_bases_and_three_step (P : ℕ → Prop)
    (hbase : ∀ n, 1 ≤ n → n ≤ 30 → P n)
    (hstep : ∀ m, 28 ≤ m → P m → P (m + 3)) :
    ∀ n, 1 ≤ n → P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnpos
    by_cases hn : n ≤ 30
    · exact hbase n hnpos hn
    · have hm : 28 ≤ n - 3 := by omega
      have hlt : n - 3 < n := by omega
      have heq : n - 3 + 3 = n := by omega
      simpa only [heq] using
        hstep (n - 3) hm (ih (n - 3) hlt (by omega))

/-- Nonnegative quotient and homology dimensions have the expected maximal-rank
values exactly when at least one of them vanishes. -/
theorem optimal_dimensions_iff (quotient homology euler : ℤ)
    (hq : 0 ≤ quotient) (hh : 0 ≤ homology)
    (heuler : quotient - homology = euler) :
    (quotient = max euler 0 ∧ homology = max (-euler) 0) ↔
      quotient = 0 ∨ homology = 0 := by
  omega

/-- If there is no homology, the Euler difference is the quotient dimension. -/
theorem dimensions_of_homology_zero (quotient homology euler : ℤ)
    (hq : 0 ≤ quotient) (heuler : quotient - homology = euler)
    (hzero : homology = 0) :
    quotient = max euler 0 ∧ homology = max (-euler) 0 := by
  omega

/-- If the products span, the negative Euler difference is the homology dimension. -/
theorem dimensions_of_quotient_zero (quotient homology euler : ℤ)
    (hh : 0 ≤ homology) (heuler : quotient - homology = euler)
    (hzero : quotient = 0) :
    quotient = max euler 0 ∧ homology = max (-euler) 0 := by
  omega

/-- Two adjacent endpoint properties propagate to every integer count when the
lower property is inherited downwards and the upper property upwards. -/
theorem endpoint_reduction (Injective Surjective : ℕ → Prop)
    (lower upper : ℕ) (hadj : upper ≤ lower + 1)
    (hlower : Injective lower) (hupper : Surjective upper)
    (hrestrict : ∀ a b, a ≤ b → Injective b → Injective a)
    (hextend : ∀ a b, a ≤ b → Surjective a → Surjective b) :
    ∀ r, Injective r ∨ Surjective r := by
  intro r
  by_cases h : r ≤ lower
  · exact Or.inl (hrestrict r lower h hlower)
  · exact Or.inr (hextend upper r (by omega) hupper)

end Quartic.Induction
