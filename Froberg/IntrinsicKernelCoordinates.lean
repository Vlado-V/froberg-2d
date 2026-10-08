import Froberg.ActualClosedKernelSlices

/-! Coordinate transport for the actual duals, relation kernels and higher
product images used by the intrinsic layered avoidance theorem. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module Quartic Quartic.BilinearCovectorCharts Quartic.BilinearCoefficientKernel
open Quartic.AmbientCovectorTransport Quartic.PolynomialBilinearCoordinates
open BilinearScalarFamily
variable {K P V W H : Type} [Field K]
  [AddCommGroup P] [Module K P] [FiniteDimensional K P]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]

def dualCoordinateEquiv : (W →ₗ[K] K) ≃ₗ[K] (Fin (finrank K W) → K) where
  toFun := dualCoordinates (coordinates K W)
  invFun ell := (covector ell).comp (coordinates K W).toLinearMap
  left_inv ell := by
    ext w
    exact (covector_dualCoordinates (coordinates K W) ell ((coordinates K W) w)).trans
      (congrArg ell ((coordinates K W).symm_apply_apply w))
  right_inv := dualCoordinates_comp_covector (coordinates K W)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordinateTensor_coordinates (mu : P →ₗ[K] V →ₗ[K] W) (p : P) (v : V) :
    coordinateTensor mu (coordinates K P p) (coordinates K V v)=coordinates K W (mu p v) := by
  simp only [coordinateTensor,transportBilinear_apply,LinearEquiv.symm_apply_apply]

@[simp] theorem covector_dualCoordinateEquiv (ell : W →ₗ[K] K) (w : W) :
    covector (dualCoordinateEquiv ell) (coordinates K W w)=ell w := by
  rw [show dualCoordinateEquiv ell=dualCoordinates (coordinates K W) ell from rfl,
    covector_dualCoordinates,LinearEquiv.symm_apply_apply]

theorem coordinateTensor_kernel (mu : P →ₗ[K] V →ₗ[K] W) (ell : W →ₗ[K] K) :
    (relationMap (coordinateTensor mu) (dualCoordinateEquiv ell)).ker=
      (QuotientCovectorKernel.relation mu ell).ker.map (coordinates K V).toLinearMap :=
  kernel_coordinates (coordinates K P) (coordinates K V) (coordinates K W) mu
    (coordinateTensor mu) (coordinateTensor_coordinates mu) ell

theorem coordinateTensor_kernel_finrank (mu : P →ₗ[K] V →ₗ[K] W) (ell : W →ₗ[K] K) :
    finrank K (relationMap (coordinateTensor mu) (dualCoordinateEquiv ell)).ker=
      finrank K (QuotientCovectorKernel.relation mu ell).ker := by
  rw [coordinateTensor_kernel,LinearEquiv.finrank_map_eq]

theorem coordinateTensor_kernel_image_finrank (mu : P →ₗ[K] V →ₗ[K] W)
    (muH : P →ₗ[K] V →ₗ[K] H) (ell : W →ₗ[K] K) :
    finrank K (BilinearImage.image (coordinateTensor muH)
      (relationMap (coordinateTensor mu) (dualCoordinateEquiv ell)).ker)=
      finrank K (BilinearImage.image muH (QuotientCovectorKernel.relation mu ell).ker) := by
  rw [coordinateTensor_kernel]
  unfold coordinateTensor
  rw [image_transportBilinear,LinearEquiv.finrank_map_eq]
  have he : ((QuotientCovectorKernel.relation mu ell).ker.map
      (coordinates K V).toLinearMap).map (coordinates K V).symm.toLinearMap=
        (QuotientCovectorKernel.relation mu ell).ker := by
    ext x
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      change (QuotientCovectorKernel.relation mu ell)
        ((coordinates K V).symm (coordinates K V z))=0
      rw [LinearEquiv.symm_apply_apply]
      exact LinearMap.mem_ker.mp hz
    · intro hx
      exact ⟨coordinates K V x,⟨x,hx,rfl⟩,(coordinates K V).symm_apply_apply x⟩
  rw [he]

end Froberg
