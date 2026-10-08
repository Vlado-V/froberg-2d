import Froberg.PrivateModelExistence
import Froberg.ScalarMaximalRankOpen

/-! The private outer models admit scalar multiplication of maximal rank. -/
noncomputable section
namespace Froberg.PrivateColumns
open Module OuterInjection AttachedMultiplication MvPolynomial
open Quartic.PolynomialBilinearCoordinates
variable {K : Type*} [Field K] [Infinite K] {a z s k b h : ℕ}

 theorem generic_private_scalar_maximal_rank (ι : Fin b ↪ Fin z)
    (u : Labels k a s ⊕ Fin b → Fin h → K) (q : ℕ) (D : ℝ)
    (hA : 0 < finrank K (PrivateSourceSpace ι u))
    (hD : (finrank K (PrivateSourceSpace ι u) : ℝ) ≤ D)
    (hgrowth : ∀ V : Submodule K (PrivateSourceSpace ι u),
      ((finrank K (PrivateTargetSpace ι u) : ℝ)/finrank K (PrivateSourceSpace ι u))*finrank K V+
        D*(min (finrank K V) (finrank K (PrivateSourceSpace ι u)-finrank K V) : ℕ) ≤
      finrank K (outerImage (d := s+1) (attachedExponent ι) u (attachedExponent_degree ι) V)) :
    ∃ P : MvPolynomial (Fin (finrank K (Fin q → Forms K (a+z) (s+1)))) K,
      (∃ Q : Fin q → Forms K (a+z) (s+1),eval (coordinates K _ Q) P ≠ 0) ∧
      ∀ Q : Fin q → Forms K (a+z) (s+1),eval (coordinates K _ Q) P ≠ 0 →
        finrank K (BilinearScalarFamily.multiplication
          (quotientMultiply (d := s+1) (attachedExponent ι) u (attachedExponent_degree ι)) Q).range =
        min (q*finrank K (PrivateSourceSpace ι u)) (finrank K (PrivateTargetSpace ι u)) :=
  BilinearScalarFamily.generic_scalar_maximal_rank _ q D hA hD hgrowth

end Froberg.PrivateColumns
