import Froberg.ThinCovectorSlices
import Froberg.BilinearScalarSurjection
import Quartic.AmbientCovectorTransport

/-! Thin covector bounds for actual vector spaces and scalar families. -/
noncomputable section
namespace Froberg.BilinearScalarFamily
open Module MvPolynomial Quartic PolynomialBilinearCoordinates
open AmbientCovectorTransport QuotientCovectorKernel
variable {K F V W : Type*} [Field K] [Infinite K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {q j : ℕ}

theorem principal_open_actual_thin_slices (mu : F →ₗ[K] V →ₗ[K] W)
    (ha : 0 < finrank K V) (hT : finrank K W=q*finrank K V+j)
    (G C : ℝ) (hC : 0 ≤ C) (hG₁ : (finrank K V : ℝ)+C ≤ G)
    (hG₂ : (finrank K V : ℝ)+(j : ℝ)/finrank K V ≤ G)
    (hgrowth : ∀ U : Submodule K V,
      ((finrank K W : ℝ)/finrank K V)*finrank K U+
        G*(min (finrank K U) (finrank K V-finrank K U) : ℕ) ≤
        finrank K (BilinearImage.image mu U)) :
    ∃ P : MvPolynomial (Fin q × Fin (finrank K F)) K,
      ∃ Z : (r : Fin (finrank K V+1)) → Fin (BilinearCovectorStrata.thinSlices j C r.val) → W,
      (∃ Q : Fin q → F,eval (fun ik => coordinates K F (Q ik.1) ik.2) P ≠ 0) ∧
      ∀ Q : Fin q → F,eval (fun ik => coordinates K F (Q ik.1) ik.2) P ≠ 0 →
        ∀ r : Fin (finrank K V+1),∀ ell : W →ₗ[K] K,
          r.val ≤ finrank K (LinearMap.ker (relation mu ell)) →
          (∀ i v,ell (mu (Q i) v)=0) → (∀ t,ell (Z r t)=0) → ell=0 := by
  let eF := coordinates K F
  let eV := coordinates K V
  let eW := coordinates K W
  let nu := transportBilinear eF eV eW mu
  have hnu : ∀ f v,nu (eF f) (eV v)=eW (mu f v) := by
    intro f v
    simp only [nu,transportBilinear_apply,LinearEquiv.symm_apply_apply]
  have hg (U : Submodule K (Fin (finrank K V) → K)) :
      ((finrank K W : ℝ)/finrank K V)*finrank K U+
        G*(min (finrank K U) (finrank K V-finrank K U) : ℕ) ≤
        finrank K (BilinearImage.image nu U) := by
    have hu := hgrowth (U.map eV.symm.toLinearMap)
    rw [eV.symm.finrank_map_eq] at hu
    change _ ≤ (finrank K (BilinearImage.image (transportBilinear eF eV eW mu) U) : ℝ)
    rw [image_transportBilinear,eW.finrank_map_eq]
    exact hu
  obtain ⟨P,Z,hP,hgood⟩ := BilinearCovectorStrata.principal_open_thin_slices
    nu ha hT G C hC hG₁ hG₂ hg
  refine ⟨P,fun r t => eW.symm (Z r t),?_,?_⟩
  · obtain ⟨Q,hQ⟩ := hP
    refine ⟨fun i => eF.symm (fun k => Q (i,k)),?_⟩
    simpa only [eF,LinearEquiv.apply_symm_apply] using hQ
  · intro Q hQ r ell hr hann hZ
    have hz : dualCoordinates eW ell=0 := by
      apply hgood (fun ik => eF (Q ik.1) ik.2) hQ r
      · rwa [kernel_coordinates_finrank eF eV eW mu nu hnu ell]
      · constructor
        · intro i v
          change BilinearCovectorCharts.covector (dualCoordinates eW ell)
            (eW (mu (eF.symm (eF (Q i))) (eV.symm v)))=0
          rw [covector_dualCoordinates,LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]
          exact hann i (eV.symm v)
        · intro t
          rw [covector_dualCoordinates]
          exact hZ t
    exact (dualCoordinates_eq_zero_iff eW ell).mp hz

end Froberg.BilinearScalarFamily
