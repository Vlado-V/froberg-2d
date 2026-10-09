module

public import Froberg.PreparedScalarFiber

@[expose] public section

/-! Freezing the remaining prepared coordinates preserves the base
family and makes the positive generators exactly E_i+a_i. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial PreparedParameters
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem scalarFiber_base (hO : ∀ j∈J,O j≤Forms K h j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (a : PositiveScalars (K := K) m d J counts) (rest : ScalarFiberRest m d q J counts O) :
    preparedBaseBiform hO hJ heven (scalarFiberCoordinates.symm (a,rest))=
      fun i => scalarEvenBiform (rest.1 i) := by
  funext i
  rw [preparedBaseBiform_eq_scalar,scalarFiberCoordinates_symm_base]

theorem scalarFiber_high (hO : ∀ j∈J,O j≤Forms K h j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (a : PositiveScalars (K := K) m d J counts) (rest : ScalarFiberRest m d q J counts O) :
    preparedHighBiform hO hJ heven (scalarFiberCoordinates.symm (a,rest))=
      preparedHighBiform hO hJ heven (scalarFiberCoordinates.symm (0,rest)) := by
  funext i
  apply Subtype.ext
  rw [preparedHighBiform_val,preparedHighBiform_val]
  rfl

theorem scalarFiber_positive (hO : ∀ j∈J,O j≤Forms K h j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (a : PositiveScalars (K := K) m d J counts) (rest : ScalarFiberRest m d q J counts O) :
    preparedPositiveBiform hO hJ heven (scalarFiberCoordinates.symm (a,rest))=
      oddEvenAffineFamily (preparedHighBiform hO hJ heven (scalarFiberCoordinates.symm (0,rest))) a := by
  rw [preparedPositiveBiform_eq_affine,scalarFiber_high]
  congr 1
  funext i
  exact scalarFiberCoordinates_symm_positive a rest i

@[simp] theorem fullScalarFiber_private
    (a : PositiveScalars (K := K) m d J counts) (rest : FullScalarFiberRest m d q f u J counts O) :
    (fullScalarFiberCoordinates.symm (a,rest)).1=rest.1 := rfl

@[simp] theorem fullScalarFiber_outer
    (a : PositiveScalars (K := K) m d J counts) (rest : FullScalarFiberRest m d q f u J counts O) :
    (fullScalarFiberCoordinates.symm (a,rest)).2.2=rest.2.2 := rfl

end Froberg.PreparedTarget
