import Quartic.BilinearImage
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Scalar extension of a coordinate bilinear map by its actual coefficient tensor -/
noncomputable section
namespace Quartic.BilinearScalarExtension
open Module
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {a b t : ℕ}

/-- Assemble a bilinear map from its coefficients in the standard coordinate bases. -/
def fromCoefficients (c : Fin b → Fin a → Fin t → K) :
    (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K) :=
  ∑ f, LinearMap.smulRight (LinearMap.proj f)
    (LinearMap.pi (fun k => ∑ v, c f v k • LinearMap.proj v))

@[simp] theorem fromCoefficients_apply (c : Fin b → Fin a → Fin t → K)
    (f : Fin b → K) (v : Fin a → K) (k : Fin t) :
    fromCoefficients c f v k = ∑ i, f i * (∑ j, c i j k * v j) := by
  simp [fromCoefficients, Finset.sum_apply]

@[simp] theorem fromCoefficients_basis_left (c : Fin b → Fin a → Fin t → K)
    (f : Fin b) (v : Fin a → K) (k : Fin t) :
    fromCoefficients c (Pi.single f 1) v k = ∑ j, c f j k * v j := by
  classical
  simp [fromCoefficients_apply, Pi.single_apply]

@[simp] theorem fromCoefficients_basis (c : Fin b → Fin a → Fin t → K)
    (f : Fin b) (v : Fin a) (k : Fin t) :
    fromCoefficients c (Pi.single f 1) (Pi.single v 1) k = c f v k := by
  classical
  rw [fromCoefficients_basis_left]
  simp [Pi.single_apply]

/-- The tensor entries are the actual products of the standard basis vectors. -/
def coefficients (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K)) :
    Fin b → Fin a → Fin t → K :=
  fun f v k => mu (Pi.single f 1) (Pi.single v 1) k

/-- Coefficient reconstruction loses none of the actual bilinear map. -/
theorem fromCoefficients_coefficients
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K)) :
    fromCoefficients (coefficients mu) = mu := by
  apply (Pi.basisFun K (Fin b)).ext
  intro f
  apply (Pi.basisFun K (Fin a)).ext
  intro v
  funext k
  simp only [Pi.basisFun_apply, fromCoefficients_basis, coefficients]

/-- Extend the actual tensor by the specified coefficient-field homomorphism. -/
def extend (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K)) :
    (Fin b → L) →ₗ[L] (Fin a → L) →ₗ[L] (Fin t → L) :=
  fromCoefficients (fun f v k => algebraMap K L (coefficients mu f v k))

@[simp] theorem extend_basis_left
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K))
    (f : Fin b) (v : Fin a → L) (k : Fin t) :
    extend (L := L) mu (Pi.single f 1) v k =
      ∑ j, algebraMap K L (mu (Pi.single f 1) (Pi.single j 1) k) * v j := by
  simp only [extend, fromCoefficients_basis_left, coefficients]

@[simp] theorem extend_basis
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K))
    (f : Fin b) (v : Fin a) (k : Fin t) :
    extend (L := L) mu (Pi.single f 1) (Pi.single v 1) k =
      algebraMap K L (mu (Pi.single f 1) (Pi.single v 1) k) := by
  simp only [extend, fromCoefficients_basis, coefficients]

@[simp] theorem extend_self
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K)) :
    extend (L := K) mu = mu := by
  simpa only [extend, Algebra.algebraMap_self, RingHom.id_apply] using fromCoefficients_coefficients mu

end Quartic.BilinearScalarExtension
