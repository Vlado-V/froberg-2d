import Froberg.LinearCutVectors
import Froberg.ActualClosedKernelSlices

/-! Closed kernel slices are exactly annihilator conditions on finitely
many actual target vectors. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg.BilinearScalarFamily
open Module MvPolynomial Quartic PolynomialBilinearCoordinates
open AmbientCovectorTransport BilinearCoefficientKernel BilinearCovectorCharts
variable {K F V W : Type*} [Field K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem hasClosedKernelSlices_iff_vectors (mu : F →ₗ[K] V →ₗ[K] W) (s : ℕ → ℕ) :
    HasClosedKernelSlices mu s ↔
      ∃ Z : (r : Fin (finrank K V+1)) → Fin (s r.val) → W,
        ∀ r (ell : W →ₗ[K] K),
          r.val ≤ finrank K (LinearMap.ker (QuotientCovectorKernel.relation mu ell)) →
          (∀ t,ell (Z r t)=0) → ell=0 := by
  constructor
  · rintro ⟨count,degrees,eqs,cuts,heq,hempty⟩
    have hex (r : Fin (finrank K V+1)) (i : Fin (s r.val)) := exists_linearCutVector (cuts r i)
    choose z hz using hex
    refine ⟨fun r i => (coordinates K W).symm (z r i),?_⟩
    intro r ell hr hZ
    have hcoord : ∀ f v,coordinateTensor mu (coordinates K F f) (coordinates K V v)=
        coordinates K W (mu f v) := by
      intros
      simp only [coordinateTensor,transportBilinear_apply,LinearEquiv.symm_apply_apply]
    have hk := kernel_coordinates_finrank (coordinates K F) (coordinates K V) (coordinates K W)
      mu (coordinateTensor mu) hcoord ell
    apply (dualCoordinates_eq_zero_iff (coordinates K W) ell).mp
    apply hempty r
    · simpa only [aeval_eq_eval] using (heq r _).mpr (hr.trans_eq hk.symm)
    · intro i
      rw [← hz r i,aeval_eq_eval,ClosedCovectorEquations.eval_linearForm,covector_dualCoordinates]
      exact hZ i
  · rintro ⟨Z,hZ⟩
    exact exists_actual_closed_kernel_slices mu s Z hZ

end Froberg.BilinearScalarFamily
