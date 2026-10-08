import Froberg.VectorQuotientDimensions
import Froberg.ScalarMaximalRankOpen

/-! The actual polynomial source, target, and strict expansion property. -/
noncomputable section
namespace Froberg.VectorExpansionOpen
open Module VectorMultiplicationCoordinates Quartic
variable {K : Type*} [Field K] {h n s d c : ℕ}

abbrev Source (g : Fin c → Rows K h n s) :=
  (Rows K h n s) ⧸ Submodule.span K (Set.range g)

abbrev Target (g : Fin c → Rows K h n s) (d : ℕ) :=
  (Rows K h n (s+d)) ⧸ BilinearImage.image (multiplication (d := d)) (Submodule.span K (Set.range g))

def quotientMultiplication (g : Fin c → Rows K h n s) (d : ℕ) :
    Forms K n d →ₗ[K] Source g →ₗ[K] Target g d :=
  QuotientBilinearImage.quotientMap (multiplication (d := d)) (Submodule.span K (Set.range g))

structure StrictModel (g : Fin c → Rows K h n s) (d : ℕ) (G : ℝ) : Prop where
  independent : LinearIndependent K g
  product_injective : Function.Injective (BilinearImage.tupleMap (multiplication (d := d)) g)
  source_pos : 0 < finrank K (Source g)
  source_le : (finrank K (Source g) : ℝ) ≤ G
  growth : ∀ U : Submodule K (Source g),
    ((finrank K (Target g d) : ℝ)/finrank K (Source g))*finrank K U+
      G*(min (finrank K U) (finrank K (Source g)-finrank K U) : ℕ) ≤
        (finrank K (BilinearImage.image (quotientMultiplication g d) U) : ℝ)

lemma StrictModel.generic_maximal_rank [Infinite K] {g : Fin c → Rows K h n s} {G : ℝ}
    (hg : StrictModel g d G) (q : ℕ) :
    ∃ P : MvPolynomial (Fin (finrank K (Fin q → Forms K n d))) K,
      (∃ Q : Fin q → Forms K n d,MvPolynomial.eval
        (Quartic.PolynomialBilinearCoordinates.coordinates K _ Q) P ≠ 0) ∧
      ∀ Q : Fin q → Forms K n d,MvPolynomial.eval
        (Quartic.PolynomialBilinearCoordinates.coordinates K _ Q) P ≠ 0 →
        finrank K (BilinearScalarFamily.multiplication (quotientMultiplication g d) Q).range=
          min (q*finrank K (Source g)) (finrank K (Target g d)) :=
  BilinearScalarFamily.generic_scalar_maximal_rank _ q G hg.source_pos hg.source_le hg.growth

end Froberg.VectorExpansionOpen
