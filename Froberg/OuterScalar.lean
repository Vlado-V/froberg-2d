import Froberg.OuterGrowthTransfer
import Froberg.BilinearScalarFamily

/-! Generic scalar multiplication in the actual attached outer quotient. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open Module MvPolynomial Quartic.PolynomialBilinearCoordinates
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I] {n s h q : ℕ}
variable (e : I → Fin n →₀ ℕ) (v : I → Fin h → K) (he : ∀ i, (e i).degree = s)

/-- An ordered tuple of actual homogeneous scalar forms multiplies in the
actual polynomial quotient. -/
abbrev scalarMultiplication (Q : Fin q → Forms K n (s+1)) :
    (Fin q → ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)) →ₗ[K]
      ((Fin h → Forms K n (s+(s+1))) ⧸ relationSpace (d := s+1) e v he) :=
  BilinearScalarFamily.multiplication (quotientMultiply (d := s+1) e v he) Q

/-- The strict outer shadow supplies the entire coefficient-incidence argument,
including a nonempty principal open of actual scalar forms. -/
theorem generic_scalar_injective [Infinite K] (R D : ℝ) (hq : (q : ℝ) ≤ R)
    (hD : (finrank K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he) : ℝ) ≤ D)
    (hgrowth : ∀ L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he),
      R*finrank K L + D*(min (finrank K L)
        (finrank K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)-finrank K L) : ℕ) ≤
      finrank K (outerImage (d := s+1) e v he L)) :
    ∃ P : MvPolynomial (Fin (finrank K (Fin q → Forms K n (s+1)))) K,
      (∃ Q : Fin q → Forms K n (s+1), eval (coordinates K _ Q) P ≠ 0) ∧
      ∀ Q : Fin q → Forms K n (s+1), eval (coordinates K _ Q) P ≠ 0 →
        Function.Injective (scalarMultiplication e v he Q) :=
  BilinearScalarFamily.generic_injective_of_strict_shadow
    (quotientMultiply (d := s+1) e v he) R D hq hD hgrowth

/-- Rank-nullity computes the actual scalar quotient at each injective point. -/
theorem scalar_quotient_finrank (Q : Fin q → Forms K n (s+1))
    (hQ : Function.Injective (scalarMultiplication e v he Q)) :
    finrank K (((Fin h → Forms K n (s+(s+1))) ⧸ relationSpace (d := s+1) e v he) ⧸
      (scalarMultiplication e v he Q).range) =
      finrank K ((Fin h → Forms K n (s+(s+1))) ⧸ relationSpace (d := s+1) e v he) -
        q*finrank K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he) :=
  BilinearScalarFamily.quotient_finrank _ Q hQ

end Froberg.AttachedMultiplication
