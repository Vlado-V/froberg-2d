module

public import Froberg.ClosedKernelSlices
public import Froberg.BilinearScalarSurjection
public import Quartic.AmbientCovectorTransport

@[expose] public section

/-! Closed kernel thresholds in coordinates of arbitrary actual vector spaces. -/
noncomputable section
namespace Froberg.BilinearScalarFamily
open Module MvPolynomial Quartic PolynomialBilinearCoordinates
open AmbientCovectorTransport BilinearCoefficientKernel BilinearCovectorCharts
variable {K F V W : Type*} [Field K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

def coordinateTensor (mu : F →ₗ[K] V →ₗ[K] W) :
    (Fin (finrank K F) → K) →ₗ[K] (Fin (finrank K V) → K) →ₗ[K] (Fin (finrank K W) → K) :=
  transportBilinear (coordinates K F) (coordinates K V) (coordinates K W) mu

def HasClosedKernelSlices (mu : F →ₗ[K] V →ₗ[K] W) (s : ℕ → ℕ) : Prop :=
  ∃ (count : Fin (finrank K V+1) → ℕ) (degrees : ∀ r,Fin (count r) → ℕ)
    (eqs : ∀ r,(i : Fin (count r)) → Forms K (finrank K W) (degrees r i))
    (cuts : ∀ r : Fin (finrank K V+1),Fin (s r.val) → Forms K (finrank K W) 1),
    (∀ r (ell : Fin (finrank K W) → K),(∀ i,eval ell (eqs r i).val=0) ↔
      r.val ≤ finrank K (LinearMap.ker (relationMap (coordinateTensor mu) ell))) ∧
    (∀ r (ell : Fin (finrank K W) → K),(∀ i,aeval ell (eqs r i).val=0) →
      (∀ t,aeval ell (cuts r t).val=0) → ell=0)

theorem exists_actual_closed_kernel_slices (mu : F →ₗ[K] V →ₗ[K] W)
    (s : ℕ → ℕ) (Z : (r : Fin (finrank K V+1)) → Fin (s r.val) → W)
    (hZ : ∀ r : Fin (finrank K V+1),∀ ell : W →ₗ[K] K,
      r.val ≤ finrank K (LinearMap.ker (QuotientCovectorKernel.relation mu ell)) →
      (∀ t,ell (Z r t)=0) → ell=0) :
    ∃ (count : Fin (finrank K V+1) → ℕ) (degrees : ∀ r,Fin (count r) → ℕ)
      (eqs : ∀ r,(i : Fin (count r)) → Forms K (finrank K W) (degrees r i))
      (cuts : ∀ r : Fin (finrank K V+1),Fin (s r.val) → Forms K (finrank K W) 1),
      (∀ r (ell : Fin (finrank K W) → K),(∀ i,eval ell (eqs r i).val=0) ↔
        r.val ≤ finrank K (LinearMap.ker (relationMap (coordinateTensor mu) ell))) ∧
      (∀ r (ell : Fin (finrank K W) → K),(∀ i,aeval ell (eqs r i).val=0) →
        (∀ t,aeval ell (cuts r t).val=0) → ell=0) := by
  apply exists_closed_kernel_slices (coordinateTensor mu) s (fun r t => coordinates K W (Z r t))
  intro r lam hr hcuts
  let ell := (covector lam).comp (coordinates K W).toLinearMap
  have hcoord : ∀ f v,coordinateTensor mu (coordinates K F f) (coordinates K V v)=
      coordinates K W (mu f v) := by
    intros
    simp only [coordinateTensor,transportBilinear_apply,LinearEquiv.symm_apply_apply]
  have hk := kernel_coordinates_finrank (coordinates K F) (coordinates K V) (coordinates K W)
    mu (coordinateTensor mu) hcoord ell
  rw [dualCoordinates_comp_covector] at hk
  have hz : ell=0 := hZ r ell (hr.trans_eq hk) hcuts
  have ht := (dualCoordinates_eq_zero_iff (coordinates K W) ell).mpr hz
  simpa only [ell,dualCoordinates_comp_covector] using ht

end Froberg.BilinearScalarFamily
