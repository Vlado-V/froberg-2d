module

public import Froberg.PresentationSliceOpen
public import Froberg.QuotientSliceVectors

@[expose] public section

/-! Persistence of all actual quotient-covector slice bounds under a
polynomial change of the target relations. No varying basis is assumed. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.BilinearScalarFamily
open Module MvPolynomial Quartic PolynomialBilinearCoordinates
open AmbientCovectorTransport BilinearCovectorCharts BilinearCoefficientKernel
variable {K F V W I : Type*} [Field K] [IsAlgClosed K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {c : ℕ}

theorem quotient_slices_principal_open (mu : F →ₗ[K] V →ₗ[K] W)
    (A : (I → K) → Fin c → W) (hA : ∀ i,IsPolynomialFamily (fun p => A p i))
    (s : ℕ → ℕ) (p₀ : I → K)
    (hzero : HasClosedKernelSlices
      (targetPostcompose mu (Submodule.span K (Set.range (A p₀))).mkQ) s) :
    ∃ P : MvPolynomial I K,eval p₀ P ≠ 0 ∧ ∀ p,eval p P ≠ 0 →
      HasClosedKernelSlices (targetPostcompose mu (Submodule.span K (Set.range (A p))).mkQ) s := by
  obtain ⟨Z,hZ⟩ := (quotient_slices_iff_lifted mu _ s).mp hzero
  let Ac : (I → K) → Fin c → Fin (finrank K W) → K :=
    fun p i => coordinates K W (A p i)
  have hAc (i : Fin c) (k : Fin (finrank K W)) : IsPolynomialFamily (fun p => Ac p i k) :=
    (hA i).linear_comp ((LinearMap.proj k).comp (coordinates K W).toLinearMap)
  have hcoord : ∀ f v,coordinateTensor mu (coordinates K F f) (coordinates K V v)=
      coordinates K W (mu f v) := by
    intros
    simp only [coordinateTensor,transportBilinear_apply,LinearEquiv.symm_apply_apply]
  let cuts : (r : Fin (finrank K V+1)) → Fin (s r.val) → Forms K (finrank K W) 1 :=
    fun r i => ClosedCovectorEquations.linearForm (coordinates K W (Z r i))
  have hempty (r : Fin (finrank K V+1)) (lam : Fin (finrank K W) → K)
      (hr : r.val ≤ finrank K (LinearMap.ker (relationMap (coordinateTensor mu) lam)))
      (hann : ∀ i,covector lam (Ac p₀ i)=0)
      (hc : ∀ i,aeval lam (cuts r i).val=0) : lam=0 := by
    let ell : W →ₗ[K] K := (covector lam).comp (coordinates K W).toLinearMap
    have hk := kernel_coordinates_finrank (coordinates K F) (coordinates K V) (coordinates K W)
      mu (coordinateTensor mu) hcoord ell
    rw [dualCoordinates_comp_covector] at hk
    have he : ell=0 := hZ r ell (hr.trans_eq hk) (by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hann i) (by
      intro i
      change covector lam (coordinates K W (Z r i))=0
      simpa only [cuts,aeval_eq_eval,ClosedCovectorEquations.eval_linearForm] using hc i)
    have hz := (dualCoordinates_eq_zero_iff (coordinates K W) ell).mpr he
    simpa only [ell,dualCoordinates_comp_covector] using hz
  obtain ⟨P,hP,hgood⟩ := presentation_slices_principal_open (coordinateTensor mu) Ac hAc s cuts p₀ hempty
  refine ⟨P,hP,?_⟩
  intro p hp
  apply (quotient_slices_iff_lifted mu _ s).mpr
  refine ⟨Z,?_⟩
  intro r ell hr hU hcuts
  apply (dualCoordinates_eq_zero_iff (coordinates K W) ell).mp
  apply hgood p hp r
  · rwa [kernel_coordinates_finrank (coordinates K F) (coordinates K V) (coordinates K W)
      mu (coordinateTensor mu) hcoord ell]
  · intro i
    rw [covector_dualCoordinates]
    change ell ((coordinates K W).symm (coordinates K W (A p i)))=0
    rw [LinearEquiv.symm_apply_apply]
    exact hU (Submodule.subset_span ⟨i,rfl⟩)
  · intro i
    simp only [cuts,aeval_eq_eval,ClosedCovectorEquations.eval_linearForm,covector_dualCoordinates,
      LinearEquiv.symm_apply_apply]
    exact hcuts i

end Froberg.BilinearScalarFamily
