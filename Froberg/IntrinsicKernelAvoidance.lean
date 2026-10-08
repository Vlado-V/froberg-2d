import Froberg.IntrinsicKernelCoordinates
import Froberg.AffineKernelProfiles
import Froberg.ParameterPullbackOpen

/-! The layered kernel avoidance theorem on actual finite-dimensional
spaces and actual dual covectors. Coordinate transport is discharged here. -/
noncomputable section
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic Quartic.BilinearCovectorCharts Quartic.BilinearCoefficientKernel
open Quartic.AmbientCovectorTransport Quartic.PolynomialBilinearCoordinates
open BilinearScalarFamily
variable {K P V V₀ W W₀ H : Type} [Field K] [Infinite K] [IsAlgClosed K]
  [AddCommGroup P] [Module K P] [FiniteDimensional K P]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup V₀] [Module K V₀] [FiniteDimensional K V₀]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup W₀] [Module K W₀] [FiniteDimensional K W₀]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
variable {q s threshold M : ℕ}

theorem intrinsic_kernel_profiles_avoid
    (mu : P →ₗ[K] V →ₗ[K] W) (nu : P →ₗ[K] V₀ →ₗ[K] W₀)
    (mu₀ : P →ₗ[K] V →ₗ[K] W₀) (muH : P →ₗ[K] V →ₗ[K] H)
    (bottom : (W →ₗ[K] K) →ₗ[K] (W₀ →ₗ[K] K))
    (higher : (W →ₗ[K] K) →ₗ[K] (H →ₗ[K] K))
    (res : ((W₀ →ₗ[K] K) × (H →ₗ[K] K)) →ₗ[K] (W →ₗ[K] K))
    (hres : ∀ ell,res (bottom ell,higher ell)=ell)
    (hcompat : ∀ ell p v,ell (mu p v)=(bottom ell) (mu₀ p v)+(higher ell) (muH p v))
    (s₀ : ℕ → ℕ) (hslices : HasClosedKernelSlices nu s₀)
    (hmono : ∀ ell : W →ₗ[K] K,bottom ell≠0 →
      finrank K (QuotientCovectorKernel.relation nu (bottom ell)).ker≤
        finrank K (QuotientCovectorKernel.relation mu ell).ker)
    (hgrowth : ∀ ell : W →ₗ[K] K,bottom ell≠0 →
      M*(finrank K (QuotientCovectorKernel.relation mu ell).ker-
        finrank K (QuotientCovectorKernel.relation nu (bottom ell)).ker)≤
        finrank K (BilinearImage.image muH (QuotientCovectorKernel.relation mu ell).ker))
    (B : Fin q → V →ₗ[K] W)
    (hcount : ∀ k : Fin (finrank K V+1),∀ k₀ : Fin (finrank K V₀+1),
      threshold≤k.val → k₀.val≤k.val →
      s₀ k₀.val+finrank K V*k.val+finrank K H<
        M*(k.val-k₀.val)+q*(finrank K V-k.val)+s) :
    ∃ Z : Fin s → W,
    ∃ D : MvPolynomial (Fin (finrank K (Fin q → P))) K,
      (∃ Q : Fin q → P,eval ((Module.finBasis K _).equivFun Q) D≠0) ∧
      ∀ Q,eval ((Module.finBasis K _).equivFun Q) D≠0 →
      ∀ ell : W →ₗ[K] K,bottom ell≠0 →
        threshold≤finrank K (QuotientCovectorKernel.relation mu ell).ker →
        ¬ ((∀ i v,ell (mu (Q i) v+B i v)=0) ∧ (∀ j,ell (Z j)=0)) := by
  classical
  let eW := dualCoordinateEquiv (K := K) (W := W)
  let e₀ := dualCoordinateEquiv (K := K) (W := W₀)
  let eH := dualCoordinateEquiv (K := K) (W := H)
  let bot := e₀.toLinearMap.comp (bottom.comp eW.symm.toLinearMap)
  let high := eH.toLinearMap.comp (higher.comp eW.symm.toLinearMap)
  let re := eW.toLinearMap.comp
    (res.comp (LinearEquiv.prodCongr e₀.symm eH.symm).toLinearMap)
  have hbot (ell : W →ₗ[K] K) : bot (eW ell)=e₀ (bottom ell) := by
    simp only [bot,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  have hhigh (ell : W →ₗ[K] K) : high (eW ell)=eH (higher ell) := by
    simp only [high,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  have hre (lam : Fin (finrank K W) → K) : re (bot lam,high lam)=lam := by
    obtain ⟨ell,rfl⟩ := eW.surjective lam
    rw [hbot,hhigh]
    simp only [re,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.prodCongr_apply,
      LinearEquiv.symm_apply_apply,hres]
  have hcomp (lam : Fin (finrank K W) → K)
      (p : Fin (finrank K P) → K) (v : Fin (finrank K V) → K) :
      covector lam (coordinateTensor mu p v)=
        covector (bot lam) (coordinateTensor mu₀ p v)+covector (high lam) (coordinateTensor muH p v) := by
    obtain ⟨ell,rfl⟩ := eW.surjective lam
    obtain ⟨p,rfl⟩ := (coordinates K P).surjective p
    obtain ⟨v,rfl⟩ := (coordinates K V).surjective v
    rw [hbot,hhigh]
    simp only [eW,e₀,eH,coordinateTensor_coordinates,covector_dualCoordinateEquiv,hcompat]
  have hmonoC (lam : Fin (finrank K W) → K) (hb : bot lam≠0) :
      finrank K (relationMap (coordinateTensor nu) (bot lam)).ker≤
        finrank K (relationMap (coordinateTensor mu) lam).ker := by
    obtain ⟨ell,rfl⟩ := eW.surjective lam
    rw [hbot] at hb ⊢
    have hb' : bottom ell≠0 := by intro hz;exact hb (by rw [hz,map_zero])
    simpa only [eW,e₀,coordinateTensor_kernel_finrank] using hmono ell hb'
  have hgrowthC (lam : Fin (finrank K W) → K) (hb : bot lam≠0) :
      M*(finrank K (relationMap (coordinateTensor mu) lam).ker-
        finrank K (relationMap (coordinateTensor nu) (bot lam)).ker)≤
        finrank K (BilinearImage.image (coordinateTensor muH)
          (relationMap (coordinateTensor mu) lam).ker) := by
    obtain ⟨ell,rfl⟩ := eW.surjective lam
    rw [hbot] at hb ⊢
    have hb' : bottom ell≠0 := by intro hz;exact hb (by rw [hz,map_zero])
    simpa only [eW,e₀,coordinateTensor_kernel_finrank,coordinateTensor_kernel_image_finrank]
      using hgrowth ell hb'
  obtain ⟨nf,degrees,eqs,cuts,heqs,hempty⟩ := hslices
  have hempty' (k₀ : Fin (finrank K V₀+1)) (t : Fin (finrank K W₀) → K)
      (hf : ∀ i,eval t (eqs k₀ i).val=0) (hc : ∀ i,eval t (cuts k₀ i).val=0) : t=0 :=
    hempty k₀ t hf hc
  have hpres (k₀ : Fin (finrank K V₀+1)) (t : Fin (finrank K W₀) → K)
      (hk : finrank K (relationMap (coordinateTensor nu) t).ker=k₀.val) :
      ∀ i,eval t (eqs k₀ i).val=0 := (heqs k₀ t).mpr hk.ge
  let BC (i : Fin q) := (coordinates K W).toLinearMap.comp ((B i).comp (coordinates K V).symm.toLinearMap)
  obtain ⟨Z,D,hD,hgood⟩ := affine_kernel_profiles_avoid
    (coordinateTensor mu) (coordinateTensor nu) (coordinateTensor mu₀) (coordinateTensor muH)
    bot high re hre hcomp (fun k₀ => s₀ k₀.val) nf degrees eqs cuts hempty' hpres hmonoC hgrowthC BC hcount
  let eQ : (Fin q → P) ≃ₗ[K] (Fin q → Fin (finrank K P) → K) :=
    LinearEquiv.piCongrRight (fun _ => coordinates K P)
  obtain ⟨D',hD',hgood'⟩ := principal_open_linear_pullback eQ.toLinearMap eQ.surjective D hD _ hgood
  refine ⟨fun j => (coordinates K W).symm (Z j),D',hD',?_⟩
  intro Q hQ ell hb hk hbad
  have hbc : bot (eW ell)≠0 := by
    rw [hbot]
    exact fun hz => hb (e₀.injective (by simpa only [map_zero] using hz))
  have hkc : threshold≤finrank K (relationMap (coordinateTensor mu) (eW ell)).ker := by
    simpa only [eW,coordinateTensor_kernel_finrank] using hk
  apply hgood' Q hQ (eW ell) hbc hkc
  constructor
  · intro i v
    obtain ⟨v,rfl⟩ := (coordinates K V).surjective v
    change covector (dualCoordinateEquiv ell)
      (coordinateTensor mu (coordinates K P (Q i)) (coordinates K V v)+BC i (coordinates K V v))=0
    have he : BC i (coordinates K V v)=coordinates K W (B i v) := by
      simp only [BC,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
    rw [coordinateTensor_coordinates,he,←map_add,covector_dualCoordinateEquiv]
    exact hbad.1 i v
  · intro j
    change covector (dualCoordinates (coordinates K W) ell) (Z j)=0
    rw [covector_dualCoordinates]
    exact hbad.2 j

end Froberg
