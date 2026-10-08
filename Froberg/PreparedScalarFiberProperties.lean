import Froberg.PreparedScalarFiberCompatibility
import Froberg.PreparedBackgroundUpper
import Froberg.PreparedScalarFiberAt

/-! The last scalar fiber preserves the actual B.5 and B.7 conclusions. -/
noncomputable section
set_option maxHeartbeats 100000
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial PreparedParameters
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem prepared_scalar_fiber_relative_injective
    (hd : 0 < d) (hdodd : d%2=1)
    (hO : ∀ j ∈ J,O j ≤ Forms K h j) (hJ : ∀ j ∈ J,j ≤ d) (heven : ∀ j ∈ J,j%2=0)
    (U : Fin u → Forms K h d) (rest : FullScalarFiberRest m d q f u J counts O)
    (a : PositiveScalars (K := K) m d J counts)
    (ha : OddCyclesExact U rest.1 (scalarFiberCoordinates.symm (a,rest.2.1),rest.2.2)) :
    Function.Injective (oddEvenRelativeMap
      (fun i => scalarEvenBiform (h := h) (rest.2.1.1 i))
      (fun i => preparedOddBiform hd hdodd U rest.1 rest.2.2 (Sum.inl i))
      (fun i => preparedOddBiform hd hdodd U rest.1 rest.2.2 (Sum.inr i))
      (oddEvenAffineFamily
        (preparedHighBiform hO hJ heven (scalarFiberCoordinates.symm (0,rest.2.1))) a)) := by
  have hi := prepared_odd_relative_injective hd hdodd hO hJ heven U rest.1
    (scalarFiberCoordinates.symm (a,rest.2.1),rest.2.2) ha
  rw [scalarFiber_base hO hJ heven a rest.2.1,
    scalarFiber_positive hO hJ heven a rest.2.1] at hi
  exact hi

theorem prepared_scalar_fiber_upper
    (hd : 0 < d) (hdodd : d%2=1)
    (hO : ∀ j ∈ J,O j ≤ Forms K h j) (hJ : ∀ j ∈ J,j ≤ d) (heven : ∀ j ∈ J,j%2=0)
    (U : Fin u → Forms K h d) (rest : FullScalarFiberRest m d q f u J counts O)
    (a : PositiveScalars (K := K) m d J counts)
    (ha : Function.Surjective (upperTargetMap (zeroScalarEndpointFamily hd hO hJ U rest.1
      (scalarFiberCoordinates.symm (a,rest.2.1),rest.2.2)))) :
    Function.Surjective (upperTargetMap (backgroundEnumeratedForms
      (Fin.append (fun i => scalarEvenBiform (h := h) (rest.2.1.1 i))
        (oddEvenAffineFamily
          (preparedHighBiform hO hJ heven (scalarFiberCoordinates.symm (0,rest.2.1))) a))
      (fun i => preparedOddBiform hd hdodd U rest.1 rest.2.2 (Sum.inl i))
      (fun i => preparedOddBiform hd hdodd U rest.1 rest.2.2 (Sum.inr i)))) := by
  have hu := prepared_background_upper hd hdodd hO hJ heven U rest.1
    (scalarFiberCoordinates.symm (a,rest.2.1),rest.2.2) ha
  rw [scalarFiber_base hO hJ heven a rest.2.1,
    scalarFiber_positive hO hJ heven a rest.2.1] at hu
  exact hu

end Froberg.PreparedTarget
