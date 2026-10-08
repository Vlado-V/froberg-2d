import Froberg.CountedBaseC4Growth
import Froberg.PreparedBaseProjection
import Froberg.RestoredBaseProjection

/-! Base quotient growth is imposed on the complete parameter space,
leaving all positive-row and private parameters free. -/
noncomputable section
set_option maxHeartbeats 700000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f u b t : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem prepared_base_growth_open (hd : 1 ≤ d)
    (hO : ∀ j∈J,O j≤Forms K h j)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (hgrowth : HasBaseC4GrowthOpen (m := m) (f := f) (q := q) hd R t) :
    letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
      FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
    ∃ D : MvPolynomial (Fin (finrank K
      (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O))) K,
      (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
        eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 →
        BaseC4GrowthProperty hd R t (preparedBaseProjection p) := by
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  obtain ⟨D,hD,hgood⟩ := hgrowth
  exact prepared_base_principal_pullback hO D hD (BaseC4GrowthProperty hd R t) hgood

theorem restored_base_ordinary_growth_open
    (hO : ∀ j∈J,O j≤Forms K h j)
    (hgrowth : HasOddScalarLayersOpen K h m d f q t) :
    letI : Module.Finite K (Space m d q J counts O) := finite_space hO
    ∃ D : MvPolynomial (Fin (finrank K (RestoredOuterSpace m d q f J counts O))) K,
      (∃ p : RestoredOuterSpace m d q f J counts O,
        eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 →
        ∀ (j : ℕ) (hj : 3 ≤ j) (hjd : j ≤ d),
          OddScalarLayerProperty t (by omega) hjd
            (oddScalarBiformParameters (restoredBaseProjection p)) := by
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  obtain ⟨D,hD,hgood⟩ := odd_scalar_forms_open hgrowth
  exact restored_base_principal_pullback hO D hD _ hgood

end Froberg.PreparedParameters
