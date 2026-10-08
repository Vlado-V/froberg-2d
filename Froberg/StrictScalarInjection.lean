import Froberg.StrictVectorModel

/-! The precise dimension inequality turns a strict vector model into a
nonempty open of injective scalar actions. -/
noncomputable section
namespace Froberg.VectorExpansionOpen
open Module MvPolynomial Quartic VectorMultiplicationCoordinates
variable {K : Type*} [Field K] [Infinite K] {h n s d c q : ℕ} {G : ℝ}

theorem StrictModel.generic_scalar_injective {g : Fin c → Rows K h n s}
    (hg : StrictModel g d G)
    (hq : q*finrank K (Source g)≤finrank K (Target g d)) :
    ∃ P : MvPolynomial (Fin (finrank K (Fin q → Forms K n d))) K,
      (∃ Q : Fin q → Forms K n d,eval (PolynomialBilinearCoordinates.coordinates K _ Q) P≠0) ∧
      ∀ Q : Fin q → Forms K n d,eval (PolynomialBilinearCoordinates.coordinates K _ Q) P≠0 →
        Function.Injective (BilinearScalarFamily.multiplication (quotientMultiplication g d) Q) := by
  apply BilinearScalarFamily.generic_injective_of_strict_shadow _ _ G _ hg.source_le hg.growth
  apply (le_div_iff₀ (show (0 : ℝ)<finrank K (Source g) by exact_mod_cast hg.source_pos)).mpr
  exact_mod_cast hq

end Froberg.VectorExpansionOpen
