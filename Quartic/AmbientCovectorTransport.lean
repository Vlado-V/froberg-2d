module

public import Quartic.ConvolutionClosedSlices
public import Quartic.ConvolutionAmbientImage
public import Quartic.QuotientCovectorKernel
public import Quartic.ConvolutionSharedSlices
public import Quartic.RowMultiplicationCoordinates

@[expose] public section

/-! Actual covector and kernel transport from quotient to fixed ambient spaces. -/
noncomputable section
namespace Quartic.AmbientCovectorTransport
open Module BilinearCovectorCharts BilinearCoefficientKernel QuotientCovectorKernel
variable {K F V W : Type*} [Field K]
  [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] {a b T : ℕ}

def dualCoordinates (e : W ≃ₗ[K] (Fin T → K)) (ell : W →ₗ[K] K) : Fin T → K :=
  fun i => ell (e.symm (Pi.single i 1))

theorem covector_dualCoordinates (e : W ≃ₗ[K] (Fin T → K)) (ell : W →ₗ[K] K)
    (x : Fin T → K) : covector (dualCoordinates e ell) x = ell (e.symm x) := by
  classical
  rw [covector_apply]
  conv_rhs => rw [← (Pi.basisFun K (Fin T)).sum_equivFun x]
  simp only [map_sum,map_smul,Pi.basisFun_apply,Pi.basisFun_equivFun,
    LinearEquiv.refl_apply,smul_eq_mul,dualCoordinates]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem dualCoordinates_eq_zero_iff (e : W ≃ₗ[K] (Fin T → K)) (ell : W →ₗ[K] K) :
    dualCoordinates e ell = 0 ↔ ell = 0 := by
  constructor
  · intro h
    ext w
    have he := covector_dualCoordinates e ell (e w)
    simpa only [h,covector_apply,Pi.zero_apply,zero_mul,Finset.sum_const_zero,
      LinearEquiv.symm_apply_apply,LinearMap.zero_apply] using he.symm
  · rintro rfl
    rfl

@[simp] theorem dualCoordinates_comp_covector (e : W ≃ₗ[K] (Fin T → K)) (lam : Fin T → K) :
    dualCoordinates e ((covector lam).comp e.toLinearMap) = lam := by
  classical
  funext i
  simp [dualCoordinates,covector_apply,Pi.single_apply]

theorem mem_relationMap_ker_iff
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (ell : Fin T → K) (v : Fin a → K) :
    v ∈ LinearMap.ker (relationMap mu ell) ↔ ∀ f, covector ell (mu f v) = 0 := by
  classical
  constructor
  · intro h f
    rw [← (Pi.basisFun K (Fin b)).sum_equivFun f]
    simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,
      Pi.basisFun_apply,Pi.basisFun_equivFun,LinearEquiv.refl_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hi : covector ell (mu (Pi.single i 1) v) = 0 := congrFun h i
    rw [hi,smul_zero]
  · intro h
    funext i
    exact h (Pi.single i 1)

/-- Fixed coordinate equivalences preserve the actual relation kernel. -/
theorem kernel_coordinates
    (eF : F ≃ₗ[K] (Fin b → K)) (eV : V ≃ₗ[K] (Fin a → K))
    (eW : W ≃ₗ[K] (Fin T → K)) (mu : F →ₗ[K] V →ₗ[K] W)
    (muC : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (hmu : ∀ f v, muC (eF f) (eV v) = eW (mu f v)) (ell : W →ₗ[K] K) :
    LinearMap.ker (relationMap muC (dualCoordinates eW ell)) =
      (LinearMap.ker (relation mu ell)).map eV.toLinearMap := by
  ext v
  rw [mem_relationMap_ker_iff]
  constructor
  · intro h
    refine ⟨eV.symm v,?_,eV.apply_symm_apply v⟩
    apply LinearMap.ext
    intro f
    have hf := h (eF f)
    rw [← eV.apply_symm_apply v,hmu,covector_dualCoordinates,eW.symm_apply_apply] at hf
    exact hf
  · rintro ⟨w,hw,rfl⟩ f
    obtain ⟨g,rfl⟩ := eF.surjective f
    change covector (dualCoordinates eW ell) (muC (eF g) (eV w)) = 0
    rw [hmu,covector_dualCoordinates,eW.symm_apply_apply]
    exact DFunLike.congr_fun hw g

theorem kernel_coordinates_finrank
    (eF : F ≃ₗ[K] (Fin b → K)) (eV : V ≃ₗ[K] (Fin a → K))
    (eW : W ≃ₗ[K] (Fin T → K)) (mu : F →ₗ[K] V →ₗ[K] W)
    (muC : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (hmu : ∀ f v, muC (eF f) (eV v) = eW (mu f v)) (ell : W →ₗ[K] K) :
    finrank K (LinearMap.ker (relationMap muC (dualCoordinates eW ell))) =
      finrank K (LinearMap.ker (relation mu ell)) := by
  rw [kernel_coordinates eF eV eW mu muC hmu ell,LinearEquiv.finrank_map_eq]

/-- The exact kernel shift for any actual quotient multiplication commuting
with the ambient maps, including the convolution's original presentation. -/
theorem kernel_finrank_of_comm [FiniteDimensional K V]
    (mu : F →ₗ[K] V →ₗ[K] W) (E : Submodule K V) (R : Submodule K W)
    (nu : F →ₗ[K] (V ⧸ E) →ₗ[K] (W ⧸ R))
    (hcomm : ∀ f v, nu f (E.mkQ v) = R.mkQ (mu f v))
    (ell : W →ₗ[K] K) (hR : R ≤ LinearMap.ker ell) :
    finrank K (LinearMap.ker (relation mu ell)) =
      finrank K (LinearMap.ker (relation nu (R.liftQ ell hR))) + finrank K E := by
  have hcomp : (relation nu (R.liftQ ell hR)).comp E.mkQ = relation mu ell := by
    ext v f
    change R.liftQ ell hR (nu f (E.mkQ v)) = ell (mu f v)
    rw [hcomm]
    rfl
  rw [← hcomp,LinearMap.ker_comp]
  exact QuotientBilinearImage.finrank_preimage E _

end Quartic.AmbientCovectorTransport

namespace Quartic.ConvolutionAmbientSlices
open Module ConvolutionFree ConvolutionFreePieces ConvolutionFreeMultiplication
open ConvolutionClosedSlices ProfileCertificate UniformEndpoint
open BilinearCoefficientKernel BilinearCovectorCharts AmbientCovectorTransport
variable {K : Type*} [Field K]

abbrev AmbientSource (K : Type*) [Field K] (m : ℕ) (upper : Bool) :=
  Target K (coreP (mixedCount m upper)+1) (freeW m (mixedCount m upper)) 1
abbrev AmbientTarget (K : Type*) [Field K] (m : ℕ) (upper : Bool) :=
  Target K (coreP (mixedCount m upper)+1) (freeW m (mixedCount m upper)) 3

/-- The literal coordinate relation kernel is smaller than the ambient kernel
by exactly the number of independent convolution columns. -/
theorem actual_kernel_shift (m : ℕ) (upper : Bool)
    (ht : 2 ≤ coreP (mixedCount m upper)+1)
    (ell : AmbientTarget K m upper →ₗ[K] K)
    (hrel : relations K (coreP (mixedCount m upper)+1) (freeW m (mixedCount m upper)) 3 ≤
      LinearMap.ker ell) :
    finrank K (LinearMap.ker (QuotientCovectorKernel.relation
      ConvolutionAmbientImage.multiplication ell)) =
      finrank K (LinearMap.ker (relationMap (actualMu m upper ht)
        (dualCoordinates (PolynomialBilinearCoordinates.coordinates K _)
          ((relations K _ _ 3).liftQ ell hrel)))) + (coreP (mixedCount m upper)+1+2) := by
  let eF := PolynomialBilinearCoordinates.coordinates K (Coeff K m upper)
  let eV := sourceCoordinates (K := K) m upper ht
  let eW := PolynomialBilinearCoordinates.coordinates K (Tgt K m upper)
  let nu := ConvolutionInitialImage.pieceBilinear (K := K)
    (t := coreP (mixedCount m upper)+1) (w := freeW m (mixedCount m upper)) (d := 1) (k := 2)
  have hcoord : ∀ f v, actualMu m upper ht (eF f) (eV v) = eW (nu f v) := by
    intro f v
    simp only [actualMu_apply,eF,eV,LinearEquiv.symm_apply_apply]
    rfl
  have hc := kernel_coordinates_finrank eF eV eW nu (actualMu m upper ht)
    hcoord ((relations K _ _ 3).liftQ ell hrel)
  have hs := kernel_finrank_of_comm ConvolutionAmbientImage.multiplication
    (relations K _ _ 1) (relations K _ _ 3) nu (fun _ _ => rfl) ell hrel
  rw [ConvolutionAmbientImage.relations_one_finrank ht] at hs
  exact hs.trans (congrArg (fun z => z + (coreP (mixedCount m upper)+1+2)) hc.symm)

theorem annihilates_relations (m : ℕ) (upper : Bool)
    (ell : AmbientTarget K m upper →ₗ[K] K)
    (hE : ∀ (f : Coeff K m upper) i,
      ell (ConvolutionAmbientImage.multiplication f
        (GenericF13Endpoint.convolutionMixed K _ _ i)) = 0) :
    relations K (coreP (mixedCount m upper)+1) (freeW m (mixedCount m upper)) 3 ≤
      LinearMap.ker ell := by
  rw [ConvolutionAmbientImage.relations_three_eq_image,
    QuotientCovectorKernel.annihilates_image_iff]
  intro f v hv
  have h : relations K (coreP (mixedCount m upper)+1) (freeW m (mixedCount m upper)) 1 ≤
      LinearMap.ker (ell.comp (ConvolutionAmbientImage.multiplication f)) := by
    rw [ConvolutionAmbientImage.relations_one_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hE f i
  exact h hv

/-- Lift the auxiliary quotient vectors and transport the exact closed-section
witness to ambient multiplication. No varying quotient basis is involved. -/
theorem transport_closed_section (m : ℕ) (upper : Bool)
    (ht : 2 ≤ coreP (mixedCount m upper)+1) (d : ℕ)
    (x : SlicedInput K m upper d)
    (hempty : ∀ lam : Fin (finrank K (Tgt K m upper)) → K,
      d ≤ finrank K (LinearMap.ker (relationMap (actualMu m upper ht) lam)) →
      ((∀ i v,covector lam (actualMu m upper ht (x.1 i) v)=0) ∧
        (∀ j,covector lam (x.2 j)=0)) → lam=0) :
    ∃ Z : Fin (sliceCount m upper d) → AmbientTarget K m upper,
      (∀ j,(relations K _ _ 3).mkQ (Z j) =
        (PolynomialBilinearCoordinates.coordinates K (Tgt K m upper)).symm (x.2 j)) ∧
      ∀ ell : AmbientTarget K m upper →ₗ[K] K,
        d+(coreP (mixedCount m upper)+1+2) ≤
          finrank K (LinearMap.ker (QuotientCovectorKernel.relation
            ConvolutionAmbientImage.multiplication ell)) →
        (∀ (f : Coeff K m upper) i,ell (ConvolutionAmbientImage.multiplication f
          (GenericF13Endpoint.convolutionMixed K _ _ i))=0) →
        (∀ i v,ell (ConvolutionAmbientImage.multiplication
          ((PolynomialBilinearCoordinates.coordinates K (Coeff K m upper)).symm (x.1 i)) v)=0) →
        (∀ j,ell (Z j)=0) → ell=0 := by
  classical
  have hlift (j : Fin (sliceCount m upper d)) :=
    (relations K (coreP (mixedCount m upper)+1) (freeW m (mixedCount m upper)) 3).mkQ_surjective
      ((PolynomialBilinearCoordinates.coordinates K (Tgt K m upper)).symm (x.2 j))
  choose Z hZ using hlift
  refine ⟨Z,hZ,?_⟩
  intro ell hker hE hQ hslice
  have hrel := annihilates_relations m upper ell hE
  let ellQ := (relations K (coreP (mixedCount m upper)+1) (freeW m (mixedCount m upper)) 3).liftQ ell hrel
  let lam := dualCoordinates (PolynomialBilinearCoordinates.coordinates K (Tgt K m upper)) ellQ
  have hd : d ≤ finrank K (LinearMap.ker (relationMap (actualMu m upper ht) lam)) := by
    have hs := actual_kernel_shift m upper ht ell hrel
    change finrank K (LinearMap.ker (QuotientCovectorKernel.relation
      ConvolutionAmbientImage.multiplication ell)) =
        finrank K (LinearMap.ker (relationMap (actualMu m upper ht) lam)) + _ at hs
    omega
  have hQ' : ∀ i v,covector lam (actualMu m upper ht (x.1 i) v)=0 := by
    intro i v
    rw [actualMu_apply,covector_dualCoordinates,LinearEquiv.symm_apply_apply]
    obtain ⟨w,hw⟩ := (relations K (coreP (mixedCount m upper)+1)
      (freeW m (mixedCount m upper)) 1).mkQ_surjective ((sourceCoordinates m upper ht).symm v)
    rw [← hw]
    exact hQ i w
  have hslice' : ∀ j,covector lam (x.2 j)=0 := by
    intro j
    rw [covector_dualCoordinates,← hZ j]
    exact hslice j
  have hlam := hempty lam hd ⟨hQ',hslice'⟩
  have heQ : ellQ=0 := (dualCoordinates_eq_zero_iff _ _).mp hlam
  exact (QuotientCovectorKernel.descended_eq_zero_iff _ ell hrel).mp heQ

end Quartic.ConvolutionAmbientSlices

namespace Quartic.ConvolutionAmbientSlices
open Module ConvolutionFree ConvolutionFreePieces ConvolutionFreeMultiplication
open ConvolutionClosedSlices ProfileCertificate UniformEndpoint
open BilinearCoefficientKernel BilinearCovectorCharts AmbientCovectorTransport
variable {K : Type*} [Field K]

/-- All ambient closed thresholds have one shared actual child tuple. The
auxiliary vectors are lifted to the actual polynomial target, not to a
formal replacement of it. -/
theorem exists_all_ambient_sections [Infinite K] (m : ℕ) (hmlo : 28 ≤ m)
    (hmhi : m ≤ 40) (upper : Bool) (ht : 2 ≤ coreP (mixedCount m upper)+1) :
    ∃ Q : Fin (upperEndpoint m) → Coeff K m upper,
      ∃ Z : (d : ConvolutionSharedSlices.Threshold m upper) →
        Fin (sliceCount m upper d.val) → AmbientTarget K m upper,
      ∀ d : ConvolutionSharedSlices.Threshold m upper,
        ∀ ell : AmbientTarget K m upper →ₗ[K] K,
        d.val+(coreP (mixedCount m upper)+1+2) ≤
          finrank K (LinearMap.ker (QuotientCovectorKernel.relation
            ConvolutionAmbientImage.multiplication ell)) →
        (∀ (f : Coeff K m upper) i,ell (ConvolutionAmbientImage.multiplication f
          (GenericF13Endpoint.convolutionMixed K _ _ i))=0) →
        (∀ i v,ell (ConvolutionAmbientImage.multiplication (Q i) v)=0) →
        (∀ j,ell (Z d j)=0) → ell=0 := by
  obtain ⟨x,hx⟩ := ConvolutionSharedSlices.exists_all_thresholds (K := K) m hmlo hmhi upper ht
  choose Z hZ hgood using fun d : ConvolutionSharedSlices.Threshold m upper =>
    transport_closed_section m upper ht d.val (x.1,x.2 d) (hx d)
  exact ⟨fun i => (PolynomialBilinearCoordinates.coordinates K (Coeff K m upper)).symm (x.1 i),
    Z,hgood⟩

open RowMultiplicationCoordinates HomogeneousCoefficientCoordinates

/-- The geometric convolution witness is now in fixed monomial coordinates
for the actual row multiplication tensor. E, Q, and Z can subsequently vary
without introducing coordinates on any varying quotient. -/
theorem exists_all_coordinate_sections [Infinite K] (m : ℕ) (hmlo : 28 ≤ m)
    (hmhi : m ≤ 40) (upper : Bool) (ht : 2 ≤ coreP (mixedCount m upper)+1) :
    ∃ Q : Fin (upperEndpoint m) → Fin (FormCount
      (coreP (mixedCount m upper)+1+freeW m (mixedCount m upper)) 2) → K,
      ∃ Z : (d : ConvolutionSharedSlices.Threshold m upper) →
        Fin (sliceCount m upper d.val) → Fin (RowCount
          (coreP (mixedCount m upper)+1+freeW m (mixedCount m upper)) 3) → K,
      ∀ d : ConvolutionSharedSlices.Threshold m upper,
        ∀ lam : Fin (RowCount (coreP (mixedCount m upper)+1+freeW m (mixedCount m upper)) 3) → K,
        d.val+(coreP (mixedCount m upper)+1+2) ≤
          finrank K (LinearMap.ker (relationMap RowMultiplicationCoordinates.coordinate lam)) →
        (∀ f i,covector lam (RowMultiplicationCoordinates.coordinate f
          (rowFiniteEquiv (GenericF13Endpoint.convolutionMixed K _ _ i)))=0) →
        (∀ i v,covector lam (RowMultiplicationCoordinates.coordinate (Q i) v)=0) →
        (∀ j,covector lam (Z d j)=0) → lam=0 := by
  obtain ⟨Q,Z,hgood⟩ := exists_all_ambient_sections (K := K) m hmlo hmhi upper ht
  refine ⟨fun i => finiteEquiv (Q i),fun d j => rowFiniteEquiv (Z d j),?_⟩
  intro d lam hker hE hQ hZ
  let ell : AmbientTarget K m upper →ₗ[K] K := (covector lam).comp rowFiniteEquiv.toLinearMap
  have hcoord : ∀ (f : Coeff K m upper) (v : AmbientSource K m upper),
      RowMultiplicationCoordinates.coordinate (finiteEquiv f) (rowFiniteEquiv v) =
        rowFiniteEquiv (ConvolutionAmbientImage.multiplication f v) := by
    intro f v
    simp only [coordinate_apply,LinearEquiv.symm_apply_apply]
    rfl
  have hk := kernel_coordinates_finrank finiteEquiv rowFiniteEquiv rowFiniteEquiv
    ConvolutionAmbientImage.multiplication RowMultiplicationCoordinates.coordinate hcoord ell
  rw [dualCoordinates_comp_covector] at hk
  have hell : ell=0 := hgood d ell (hk ▸ hker) (by
    intro f i
    have h := hE (finiteEquiv f) i
    rw [coordinate_apply,LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply] at h
    exact h) (by
    intro i v
    have h := hQ i (rowFiniteEquiv v)
    rw [coordinate_apply,LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply] at h
    exact h) hZ
  have hz := (dualCoordinates_eq_zero_iff rowFiniteEquiv ell).mpr hell
  rwa [dualCoordinates_comp_covector] at hz

end Quartic.ConvolutionAmbientSlices
