import Froberg.OuterScalar
import Froberg.BilinearScalarSurjection

/-! Scalar surjectivity in the genuine attached outer quotient. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open Module MvPolynomial Quartic.PolynomialBilinearCoordinates
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I] {n s h q : ℕ}
variable (e : I → Fin n →₀ ℕ) (v : I → Fin h → K) (he : ∀ i, (e i).degree=s)

theorem generic_scalar_surjective [Infinite K] (R D : ℝ)
    (hT : (finrank K ((Fin h → Forms K n (s+(s+1))) ⧸ relationSpace (d := s+1) e v he) : ℝ) =
      R*finrank K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he))
    (hq : R ≤ q) (hD : (finrank K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he) : ℝ) ≤ D)
    (hgrowth : ∀ L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he),
      R*finrank K L+D*(min (finrank K L)
        (finrank K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)-finrank K L) : ℕ) ≤
        finrank K (outerImage (d := s+1) e v he L)) :
    ∃ P : MvPolynomial (Fin q × Fin (finrank K (Forms K n (s+1)))) K,
      (∃ Q : Fin q → Forms K n (s+1), eval (fun ij => coordinates K _ (Q ij.1) ij.2) P ≠ 0) ∧
      ∀ Q : Fin q → Forms K n (s+1), eval (fun ij => coordinates K _ (Q ij.1) ij.2) P ≠ 0 →
        Function.Surjective (scalarMultiplication e v he Q) :=
  BilinearScalarFamily.generic_surjective_actual_of_strict_shadow
    (quotientMultiply (d := s+1) e v he) R D hT hq hD hgrowth

end Froberg.AttachedMultiplication
