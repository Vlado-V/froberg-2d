import Froberg.PreparedScalarFiberProperties

/-! Fixing the remaining prepared parameters at a previously chosen point
preserves the actual relative injection and upper-target surjection on
one nonempty open in all positive scalar coefficients. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial PreparedParameters
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem prepared_scalar_old_open_at
    (hd : 0 < d) (hdodd : d%2=1)
    (hO : ∀ j ∈ J,O j ≤ Forms K h j) (hJ : ∀ j ∈ J,j ≤ d)
    (heven : ∀ j ∈ J,j%2=0) (U : Fin u → Forms K h d) :
    letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
      FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
    ∀ (D : MvPolynomial (Fin (finrank K
      (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O))) K)
      (p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O),
      eval ((Module.finBasis K _).equivFun p) D ≠ 0 →
      (∀ x, eval ((Module.finBasis K _).equivFun x) D ≠ 0 →
        OddCyclesExact U x.1 x.2 ∧
        Function.Surjective (upperTargetMap (zeroScalarEndpointFamily hd hO hJ U x.1 x.2))) →
      let rest := (fullScalarFiberCoordinates p).2
      ∃ P₀ : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) m d J counts))) K,
        eval ((Module.finBasis K _).equivFun (fullScalarFiberCoordinates p).1) P₀ ≠ 0 ∧
        ∀ a, eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 →
          eval ((Module.finBasis K _).equivFun (fullScalarFiberCoordinates.symm (a,rest))) D ≠ 0 ∧
          Function.Injective (oddEvenRelativeMap
            (fun i => scalarEvenBiform (h := h) (rest.2.1.1 i))
            (fun i => preparedOddBiform hd hdodd U rest.1 rest.2.2 (Sum.inl i))
            (fun i => preparedOddBiform hd hdodd U rest.1 rest.2.2 (Sum.inr i))
            (oddEvenAffineFamily
              (preparedHighBiform hO hJ heven (scalarFiberCoordinates.symm (0,rest.2.1))) a)) ∧
          Function.Surjective (upperTargetMap (backgroundEnumeratedForms
            (Fin.append (fun i => scalarEvenBiform (h := h) (rest.2.1.1 i))
              (oddEvenAffineFamily
                (preparedHighBiform hO hJ heven (scalarFiberCoordinates.symm (0,rest.2.1))) a))
            (fun i => preparedOddBiform hd hdodd U rest.1 rest.2.2 (Sum.inl i))
            (fun i => preparedOddBiform hd hdodd U rest.1 rest.2.2 (Sum.inr i)))) := by
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  intro D p hp hgood
  obtain ⟨P₀,hP₀,hfiber⟩ := principal_open_positive_scalar_fiber_at hO D p hp
  refine ⟨P₀,hP₀,?_⟩
  intro a ha
  have hx := hfiber a ha
  have hg := hgood _ hx
  exact ⟨hx,
    prepared_scalar_fiber_relative_injective hd hdodd hO hJ heven U _ a hg.1,
    prepared_scalar_fiber_upper hd hdodd hO hJ heven U _ a hg.2⟩

end Froberg.PreparedTarget
