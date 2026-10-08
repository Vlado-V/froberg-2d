import Froberg.PreparedScalarFiber
import Froberg.FreezeAtPoint

/-! The actual scalar fiber through a previously selected good prepared point. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem principal_open_positive_scalar_fiber_at (hO : ∀ j ∈ J, O j ≤ Forms K h j) :
    letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
      FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
    ∀ (D : MvPolynomial (Fin (finrank K
      (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O))) K)
      (p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O),
      eval ((Module.finBasis K _).equivFun p) D ≠ 0 →
      ∃ E : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) m d J counts))) K,
        eval ((Module.finBasis K _).equivFun (fullScalarFiberCoordinates p).1) E ≠ 0 ∧
        ∀ a, eval ((Module.finBasis K _).equivFun a) E ≠ 0 →
          eval ((Module.finBasis K _).equivFun
            (fullScalarFiberCoordinates.symm (a,(fullScalarFiberCoordinates p).2))) D ≠ 0 := by
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  intro D p hp
  apply principal_open_freeze_at fullScalarFiberCoordinates.symm.toLinearMap
    (fullScalarFiberCoordinates p).1 (fullScalarFiberCoordinates p).2 D
  simpa only [LinearEquiv.coe_toLinearMap, Prod.eta, LinearEquiv.symm_apply_apply] using hp

end Froberg.PreparedParameters
