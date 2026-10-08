import Quartic.ExpansionClosedSlices
import Quartic.ExpansionCommonOpen
import Quartic.AmbientCovectorTransport

/-! Actual quotient multiplication on the large-range expansion locus. -/
noncomputable section
namespace Quartic.ActualExpansionSlices
open Module MvPolynomial RowMultiplicationCoordinates HomogeneousCoefficientCoordinates
open UniformEndpoint ProfileCertificate PolynomialBilinearCoordinates
open BilinearCovectorCharts BilinearCoefficientKernel ConvolutionClosedSlices
variable {K : Type*} [Field K] {m c : ℕ}
set_option maxHeartbeats 1500000

/-- Products of actual row-linear forms with quadrics span every row-cubic. -/
theorem row_image_top : BilinearImage.image (multiplication (K := K) (m := m)) ⊤=⊤ := by
  classical
  let L := Module.finBasis K (Forms K m 1)
  have hsurj : Function.Surjective (CubicGeneric.coefficientMap L) := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    rw [CubicGeneric.coefficientMap_finrank,L.span_eq,finrank_top]
    simp [finrank_forms]
  apply top_unique
  intro w _
  have hj (j : Fin 3) : Pi.single j (w j) ∈ BilinearImage.image multiplication ⊤ := by
    obtain ⟨f,hf⟩ := hsurj (w j)
    have he : Pi.single j (w j)=∑ i,multiplication (f i) (Pi.single j (L i)) := by
      rw [←hf]
      funext r
      apply Subtype.ext
      by_cases hr : r=j
      · subst r
        simp [multiplication_val,CubicGeneric.coefficientMap_val,mul_comm]
      · simp [hr,multiplication_val]
    rw [he]
    exact Submodule.sum_mem _ (fun i _ => BilinearImage.product_mem _ _ _ _ (Submodule.mem_top))
  have he : ∑ j : Fin 3,Pi.single j (w j)=w := by ext j; simp
  rw [←he]
  exact Submodule.sum_mem _ (fun j _ => hj j)

abbrev MixedSpace (g : Fin c → Rows K m 1) := Submodule.span K (Set.range g)
abbrev Relations (g : Fin c → Rows K m 1) := BilinearImage.image multiplication (MixedSpace g)
abbrev Source (g : Fin c → Rows K m 1) := (Rows K m 1) ⧸ MixedSpace g
abbrev Target (g : Fin c → Rows K m 1) := (Rows K m 3) ⧸ Relations g

def quotientMul (g : Fin c → Rows K m 1) := QuotientBilinearImage.quotientMap multiplication (MixedSpace g)

theorem quotient_image_top (g : Fin c → Rows K m 1) : BilinearImage.image (quotientMul g) ⊤=⊤ := by
  rw [quotientMul,QuotientBilinearImage.image_eq_map multiplication (MixedSpace g) (Relations g)
    (QuotientBilinearImage.quotientMap multiplication (MixedSpace g)) (fun _ _ => rfl)]
  rw [Submodule.comap_top,row_image_top,Submodule.map_top]
  exact (Relations g).range_mkQ

/-- The literal quotient multiplication, using fixed coordinate equivalences
only after the mixed presentation has been fixed. -/
def actualMu {a T : ℕ} (g : Fin c → Rows K m 1)
    (eV : Source g ≃ₗ[K] (Fin a → K)) (eW : Target g ≃ₗ[K] (Fin T → K)) :
    (Fin (FormCount m 2) → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K) :=
  (conjugate eV eW (quotientMul g)).comp finiteEquiv.symm.toLinearMap

theorem actual_image {a T : ℕ} (g : Fin c → Rows K m 1)
    (eV : Source g ≃ₗ[K] (Fin a → K)) (eW : Target g ≃ₗ[K] (Fin T → K))
    (S : Submodule K (Fin a → K)) :
    BilinearImage.image (actualMu g eV eW) S=
      (BilinearImage.image (quotientMul g) (S.map eV.symm.toLinearMap)).map eW.toLinearMap := by
  rw [actualMu,image_precompose,image_conjugate]

theorem actual_image_finrank {a T : ℕ} (g : Fin c → Rows K m 1)
    (eV : Source g ≃ₗ[K] (Fin a → K)) (eW : Target g ≃ₗ[K] (Fin T → K))
    (S : Submodule K (Fin a → K)) :
    finrank K (BilinearImage.image (actualMu g eV eW) S)=
      finrank K (BilinearImage.image (quotientMul g) (S.map eV.symm.toLinearMap)) := by
  rw [actual_image,LinearEquiv.finrank_map_eq]

theorem actual_image_top {a T : ℕ} (g : Fin c → Rows K m 1)
    (eV : Source g ≃ₗ[K] (Fin a → K)) (eW : Target g ≃ₗ[K] (Fin T → K)) :
    BilinearImage.image (actualMu g eV eW) ⊤=⊤ := by
  rw [actual_image,Submodule.map_top,eV.symm.range,quotient_image_top,Submodule.map_top,eW.range]

/-- The endpoint signs are available uniformly, including the finite range. -/
theorem dimension_signs (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    0 < Counts.j m (upperEndpoint m) (mixedCount m upper) ∧
    0 ≤ Counts.H m (upperEndpoint m) (mixedCount m upper) ∧
    0 ≤ Counts.delta m (upperEndpoint m) := by
  by_cases hs : m ≤ 319
  · have h := FiniteCounts.structural_dimension_signs m hm hs upper
    rw [←upperEndpoint_eq_table m (by omega),←mixedCount_eq_table m hs upper] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have h := UniformScalar.structural_dimension_signs m (by omega) upper
    exact ⟨h.1,h.2.1,h.2.2.1⟩

def correctionCount (m : ℕ) (upper : Bool) : ℕ :=
  (Counts.H m (upperEndpoint m) (mixedCount m upper)+3+Counts.delta m (upperEndpoint m)).toNat

def slices (m : ℕ) (upper : Bool) : ℕ → ℕ :=
  ExpansionClosedSlices.sliceCount (2*m+2*mixedCount m upper) (correctionCount m upper)
    (mixedCount m upper) (Counts.j m (upperEndpoint m) (mixedCount m upper)).toNat

theorem correctionCount_cast (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    (correctionCount m upper:ℤ)=Counts.H m (upperEndpoint m) (mixedCount m upper)+3+
      Counts.delta m (upperEndpoint m) := by
  have h := dimension_signs m hm upper
  exact Int.toNat_of_nonneg (by omega)

/-- The actual quotient target has precisely the integer source count T. -/
theorem target_finrank_cast (g : Fin c → Rows K m 1) (hg : LinearIndependent K g)
    (e₀ : ℕ) (hzero : RowExpansionOpen.Expands g c (e₀+c*(m+1).choose 2)) :
    (finrank K (Target g):ℤ)=UniformScalar.targetCount m c := by
  have h := (Relations g).finrank_quotient_add_finrank
  have hr := ExpansionCommonOpen.relation_finrank_of_zero_expansion g hg e₀ hzero
  change finrank K (Target g)+finrank K (Relations g)=finrank K (Rows K m 3) at h
  change finrank K (Relations g)=c*(m+1).choose 2 at hr
  rw [hr] at h
  have hd : finrank K (Rows K m 3)=3*(m+2).choose 3 := by
    simp [Rows,Module.finrank_pi_fintype,finrank_forms]
  rw [hd] at h
  have hZ := congrArg (fun n : ℕ => (n:ℤ)) h
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hZ
  unfold UniformScalar.targetCount Counts.b2 Counts.b3
  omega

/-- Exact quotient-target surplus at the canonical endpoints. -/
theorem surplus_cast (m : ℕ) (hm : 28 ≤ m) (upper : Bool)
    (g : Fin (mixedCount m upper) → Rows K m 1) (hg : LinearIndependent K g)
    (e₀ : ℕ) (hzero : RowExpansionOpen.Expands g (mixedCount m upper)
      (e₀+mixedCount m upper*(m+1).choose 2)) :
    upperEndpoint m*totalA m (mixedCount m upper) ≤ finrank K (Target g) ∧
    ((finrank K (Target g)-upperEndpoint m*totalA m (mixedCount m upper):ℕ):ℤ)=
      Counts.j m (upperEndpoint m) (mixedCount m upper) := by
  have ht := target_finrank_cast g hg e₀ hzero
  have hc := ConvolutionAllRange.endpoint_columns_range m hm upper
  have ha := totalA_eq m _ hc.1 hc.2
  have hj := (dimension_signs m hm upper).1
  have he : (finrank K (Target g):ℤ)-(upperEndpoint m:ℤ)*totalA m (mixedCount m upper)=
      Counts.j m (upperEndpoint m) (mixedCount m upper) := by
    rw [ht,ha,Nat.cast_sub (by omega : mixedCount m upper ≤ 3*m)]
    unfold UniformScalar.targetCount Counts.j Counts.beta Counts.alpha
    push_cast
    ring
  have hle : upperEndpoint m*totalA m (mixedCount m upper) ≤ finrank K (Target g) := by
    have : (upperEndpoint m:ℤ)*totalA m (mixedCount m upper) ≤ (finrank K (Target g):ℤ) := by omega
    exact_mod_cast this
  exact ⟨hle,by rw [Nat.cast_sub hle,Nat.cast_mul]; exact he⟩

/-- The attained ambient expansion bounds become the scalar incidence
bounds for every actual quotient subspace. -/
theorem actual_scalar_bounds (m : ℕ) (hm : 28 ≤ m) (upper : Bool)
    (g : Fin (mixedCount m upper) → Rows K m 1) (hg : LinearIndependent K g)
    (E : ConvolutionExpansionOpen.Dimensions m upper → ℕ)
    (hE : ConvolutionExpansionOpen.Thresholds m upper E)
    (hexp : ∀ d : ConvolutionExpansionOpen.Dimensions m upper,RowExpansionOpen.Expands g
      (d.val+mixedCount m upper) (E d+mixedCount m upper*(m+1).choose 2))
    (eV : Source g ≃ₗ[K] (Fin (totalA m (mixedCount m upper)) → K))
    (eW : Target g ≃ₗ[K] (Fin (finrank K (Target g)) → K))
    (S : Submodule K (Fin (totalA m (mixedCount m upper)) → K))
    (hlo : 0 < finrank K S) (hhi : finrank K S < totalA m (mixedCount m upper)) :
    let T := finrank K (Target g)
    let a := totalA m (mixedCount m upper)
    let e := finrank K (BilinearImage.image (actualMu g eV eW) S)
    UniformScalar.covectorR ((T-upperEndpoint m*a:ℕ):ℝ) e (upperEndpoint m) a (finrank K S) < 0 ∨
      UniformScalar.covectorR ((T-upperEndpoint m*a:ℕ):ℝ) e (upperEndpoint m) a (finrank K S) -
        UniformScalar.codimensionR (2*m+2*mixedCount m upper) (correctionCount m upper)
          (mixedCount m upper) (finrank K S) ≤
        max (((T-upperEndpoint m*a:ℕ):ℝ)-((2*m+2*mixedCount m upper+correctionCount m upper:ℕ):ℝ)) 0-1 := by
  let d : ConvolutionExpansionOpen.Dimensions m upper := ⟨finrank K S,by omega⟩
  have hz := hexp 0
  simp only [Fin.val_zero,zero_add] at hz
  have himage : E d ≤ finrank K (BilinearImage.image (actualMu g eV eW) S) := by
    rw [actual_image_finrank]
    apply ExpansionCommonOpen.quotient_expansion g hg (E 0) hz (hexp d)
    exact eV.symm.finrank_map_eq S
  have hb := ((hE d).2 hlo hhi).mono (E' := (finrank K (BilinearImage.image (actualMu g eV eW) S):ℝ)) (by exact_mod_cast himage)
  have hcounts := HullCertificate.scalars_original_counts m (upperEndpoint m) (mixedCount m upper)
  have hsur := (surplus_cast m hm upper g hg (E 0) hz).2
  have hsurR : ((finrank K (Target g)-upperEndpoint m*totalA m (mixedCount m upper):ℕ):ℝ)=
      (Counts.j m (upperEndpoint m) (mixedCount m upper):ℝ) := by exact_mod_cast hsur
  have hcorR : (correctionCount m upper:ℝ)=(Counts.H m (upperEndpoint m) (mixedCount m upper):ℝ)+3+
      (Counts.delta m (upperEndpoint m):ℝ) := by exact_mod_cast correctionCount_cast m hm upper
  have htotR : (Counts.hTotal m (upperEndpoint m) (mixedCount m upper):ℝ)=
      ((2*m+2*mixedCount m upper+correctionCount m upper:ℕ):ℝ) := by
    unfold Counts.hTotal Counts.k31
    push_cast
    rw [hcorR]
    ring
  have hs := hb.2
  simp only [HullCertificate.codimension,HullCertificate.target] at hs
  rw [hcounts.1,hcounts.2.1,hcounts.2.2.1,hcounts.2.2.2] at hs
  simp only [HullCertificate.scalars,Counts.k31,Int.cast_max,Int.cast_add,Int.cast_sub,
    Int.cast_mul,Int.cast_natCast,Int.cast_zero,Int.cast_ofNat,d] at hs
  dsimp only
  rw [hsurR]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,hcorR,UniformScalar.codimensionR]
  rw [htotR] at hs
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,hcorR] at hs
  simpa only [Int.cast_one] using hs

/-- On an actual expanded mixed presentation, one genuine principal open
chooses a shared child tuple and all closed-threshold slices. -/
theorem principal_open_actual_slices [Infinite K] (m : ℕ) (hm : 28 ≤ m) (upper : Bool)
    (g : Fin (mixedCount m upper) → Rows K m 1) (hg : LinearIndependent K g)
    (E : ConvolutionExpansionOpen.Dimensions m upper → ℕ)
    (hE : ConvolutionExpansionOpen.Thresholds m upper E)
    (hexp : ∀ d : ConvolutionExpansionOpen.Dimensions m upper,RowExpansionOpen.Expands g
      (d.val+mixedCount m upper) (E d+mixedCount m upper*(m+1).choose 2))
    (eV : Source g ≃ₗ[K] (Fin (totalA m (mixedCount m upper)) → K))
    (eW : Target g ≃ₗ[K] (Fin (finrank K (Target g)) → K)) :
    ∃ P : MvPolynomial (Fin (finrank K (ExpansionClosedSlices.Input K
        (totalA m (mixedCount m upper)) (FormCount m 2) (finrank K (Target g))
        (upperEndpoint m) (slices m upper)))) K,
      (∃ x : ExpansionClosedSlices.Input K (totalA m (mixedCount m upper)) (FormCount m 2)
        (finrank K (Target g)) (upperEndpoint m) (slices m upper),eval (coordinates K _ x) P ≠ 0) ∧
      ∀ x : ExpansionClosedSlices.Input K (totalA m (mixedCount m upper)) (FormCount m 2)
          (finrank K (Target g)) (upperEndpoint m) (slices m upper),eval (coordinates K _ x) P ≠ 0 →
        ∀ d : ConvolutionExpansionOpen.Dimensions m upper,∀ ell : Fin (finrank K (Target g)) → K,
          d.val ≤ finrank K (LinearMap.ker (relationMap (actualMu g eV eW) ell)) →
          ((∀ i v,covector ell (actualMu g eV eW (x.1 i) v)=0) ∧
            (∀ j,covector ell (x.2 d j)=0)) → ell=0 := by
  have hz := hexp 0
  simp only [Fin.val_zero,zero_add] at hz
  have hsur := surplus_cast m hm upper g hg (E 0) hz
  have hsurN : finrank K (Target g)-upperEndpoint m*totalA m (mixedCount m upper)=
      (Counts.j m (upperEndpoint m) (mixedCount m upper)).toNat := by omega
  apply ExpansionClosedSlices.principal_open_all_thresholds (actualMu g eV eW)
    (slices m upper) (ExpansionClosedSlices.sliceCount_antitone _ _ _ _)
  intro ell hell
  have h := ExpansionClosedSlices.strict_count_of_scalar (actualMu g eV eW)
    (2*m+2*mixedCount m upper) (correctionCount m upper) (mixedCount m upper) hsur.1
    (actual_image_top g eV eW) (by
      intro S hlo hhi
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using
        actual_scalar_bounds m hm upper g hg E hE hexp eV eW S hlo hhi) ell hell
  simpa only [hsurN,slices] using h

/-- Products with the mixed generators are exactly the relations killed
before quotient covectors are formed. -/
theorem annihilates_relations (g : Fin c → Rows K m 1) (ell : Rows K m 3 →ₗ[K] K)
    (hE : ∀ j f,ell (multiplication f (g j))=0) : Relations g ≤ LinearMap.ker ell := by
  apply iSup_le
  intro f
  rintro z ⟨v,hv,rfl⟩
  have hh : MixedSpace g ≤ LinearMap.ker (ell.comp (multiplication f)) := by
    apply Submodule.span_le.mpr
    rintro z ⟨j,rfl⟩
    exact hE j f
  exact hh hv

/-- Any actual quotient-slice witness lifts to literal row-cubic slices.
This retains both shared child coefficients and the exact ambient kernel shift. -/
theorem lift_closed_slices {a T q : ℕ} (g : Fin c → Rows K m 1) (hg : LinearIndependent K g)
    (eV : Source g ≃ₗ[K] (Fin a → K)) (eW : Target g ≃ₗ[K] (Fin T → K))
    (s : ℕ → ℕ) (x : ExpansionClosedSlices.Input K a (FormCount m 2) T q s)
    (hx : ∀ d : Fin (a+1),∀ lam : Fin T → K,
      d.val ≤ finrank K (LinearMap.ker (relationMap (actualMu g eV eW) lam)) →
      ((∀ i v,covector lam (actualMu g eV eW (x.1 i) v)=0) ∧
        (∀ j,covector lam (x.2 d j)=0)) → lam=0) :
    ∃ Z : (d : Fin (a+1)) → Fin (s d.val) → Rows K m 3,
      ∀ d : Fin (a+1),∀ ell : Rows K m 3 →ₗ[K] K,
        d.val+c ≤ finrank K (LinearMap.ker (QuotientCovectorKernel.relation multiplication ell)) →
        (∀ j f,ell (multiplication f (g j))=0) →
        (∀ i v,ell (multiplication (finiteEquiv.symm (x.1 i)) v)=0) →
        (∀ j,ell (Z d j)=0) → ell=0 := by
  classical
  choose Z hZ using fun d j => (Relations g).mkQ_surjective (eW.symm (x.2 d j))
  refine ⟨Z,?_⟩
  intro d ell hd hE hQ hslice
  have hR := annihilates_relations g ell hE
  let ellQ := (Relations g).liftQ ell hR
  let lam := AmbientCovectorTransport.dualCoordinates eW ellQ
  have hcomm : ∀ f v,actualMu g eV eW (finiteEquiv f) (eV v)=eW (quotientMul g f v) := by
    intro f v
    simp only [actualMu,LinearMap.comp_apply,conjugate_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  have hk := AmbientCovectorTransport.kernel_coordinates_finrank finiteEquiv eV eW
    (quotientMul g) (actualMu g eV eW) hcomm ellQ
  have hshift := AmbientCovectorTransport.kernel_finrank_of_comm multiplication (MixedSpace g)
    (Relations g) (quotientMul g) (fun _ _ => rfl) ell hR
  have hdim : finrank K (MixedSpace g)=c := by
    rw [MixedSpace,finrank_span_eq_card hg,Fintype.card_fin]
  rw [hdim] at hshift
  have hzero : lam=0 := by
    apply hx d lam
    · change _ ≤ finrank K (LinearMap.ker (relationMap _
        (AmbientCovectorTransport.dualCoordinates eW ellQ)))
      rw [hk]
      change finrank K (LinearMap.ker (QuotientCovectorKernel.relation multiplication ell))=
        finrank K (LinearMap.ker (QuotientCovectorKernel.relation (quotientMul g) ellQ))+c at hshift
      exact Nat.le_of_add_le_add_right (hd.trans_eq hshift)
    · constructor
      · intro i v
        change covector (AmbientCovectorTransport.dualCoordinates eW ellQ) _=0
        rw [actualMu,LinearMap.comp_apply,conjugate_apply,
          AmbientCovectorTransport.covector_dualCoordinates,LinearEquiv.symm_apply_apply]
        obtain ⟨w,hw⟩ := (MixedSpace g).mkQ_surjective (eV.symm v)
        rw [←hw]
        exact hQ i w
      · intro j
        change covector (AmbientCovectorTransport.dualCoordinates eW ellQ) _=0
        rw [AmbientCovectorTransport.covector_dualCoordinates,←hZ d j]
        exact hslice j
  have heQ : ellQ=0 := (AmbientCovectorTransport.dualCoordinates_eq_zero_iff eW ellQ).mp hzero
  apply LinearMap.ext
  intro w
  have hh := DFunLike.congr_fun heQ ((Relations g).mkQ w)
  exact hh

/-- The lifted slices in the fixed ambient monomial coordinates used by
the two actual motion matrices. -/
theorem lift_closed_slices_coordinates {a T q : ℕ} (g : Fin c → Rows K m 1)
    (hg : LinearIndependent K g)
    (eV : Source g ≃ₗ[K] (Fin a → K)) (eW : Target g ≃ₗ[K] (Fin T → K))
    (s : ℕ → ℕ) (x : ExpansionClosedSlices.Input K a (FormCount m 2) T q s)
    (hx : ∀ d : Fin (a+1),∀ lam : Fin T → K,
      d.val ≤ finrank K (LinearMap.ker (relationMap (actualMu g eV eW) lam)) →
      ((∀ i v,covector lam (actualMu g eV eW (x.1 i) v)=0) ∧
        (∀ j,covector lam (x.2 d j)=0)) → lam=0) :
    ∃ Z : (d : Fin (a+1)) → Fin (s d.val) → Rows K m 3,
      ∀ d : Fin (a+1),∀ lam : Fin (RowCount m 3) → K,
        d.val+c ≤ finrank K (LinearMap.ker (relationMap RowMultiplicationCoordinates.coordinate lam)) →
        (∀ j f,covector lam (RowMultiplicationCoordinates.coordinate f (rowFiniteEquiv (g j)))=0) →
        (∀ i v,covector lam (RowMultiplicationCoordinates.coordinate (x.1 i) v)=0) →
        (∀ j,covector lam (rowFiniteEquiv (Z d j))=0) → lam=0 := by
  obtain ⟨Z,hZ⟩ := lift_closed_slices g hg eV eW s x hx
  refine ⟨Z,?_⟩
  intro d lam hd hE hQ hslice
  let ell := (covector lam).comp rowFiniteEquiv.toLinearMap
  have hcoord : ∀ (f : Forms K m 2) (v : Rows K m 1),RowMultiplicationCoordinates.coordinate (finiteEquiv f) (rowFiniteEquiv v)=
      rowFiniteEquiv (multiplication f v) := by
    intro f v
    simp only [RowMultiplicationCoordinates.coordinate_apply,LinearEquiv.symm_apply_apply]
  have hker := AmbientCovectorTransport.kernel_coordinates_finrank finiteEquiv rowFiniteEquiv rowFiniteEquiv
    multiplication RowMultiplicationCoordinates.coordinate hcoord ell
  have hdual : AmbientCovectorTransport.dualCoordinates rowFiniteEquiv ell=lam :=
    AmbientCovectorTransport.dualCoordinates_comp_covector rowFiniteEquiv lam
  rw [hdual] at hker
  have hz : ell=0 := by
    apply hZ d ell
    · exact hd.trans_eq hker
    · intro j f
      have hh := hE j (finiteEquiv f)
      simpa only [hcoord,ell,LinearMap.comp_apply,LinearEquiv.coe_coe] using hh
    · intro i v
      have hh := hQ i (rowFiniteEquiv v)
      simpa only [RowMultiplicationCoordinates.coordinate_apply,LinearEquiv.symm_apply_apply,
        ell,LinearMap.comp_apply,LinearEquiv.coe_coe] using hh
    · exact hslice
  rw [←hdual]
  exact (AmbientCovectorTransport.dualCoordinates_eq_zero_iff rowFiniteEquiv ell).mpr hz

/-- An arbitrary additional child-coefficient principal open can be
intersected without changing the fixed mixed presentation or any threshold. -/
theorem exists_ambient_slices_in_open [Infinite K] (m : ℕ) (hm : 28 ≤ m) (upper : Bool)
    (g : Fin (mixedCount m upper) → Rows K m 1) (hg : LinearIndependent K g)
    (E : ConvolutionExpansionOpen.Dimensions m upper → ℕ)
    (hE : ConvolutionExpansionOpen.Thresholds m upper E)
    (hexp : ∀ d : ConvolutionExpansionOpen.Dimensions m upper,RowExpansionOpen.Expands g
      (d.val+mixedCount m upper) (E d+mixedCount m upper*(m+1).choose 2))
    (D : MvPolynomial (Fin (upperEndpoint m) × Fin (FormCount m 2)) K)
    (hD : ∃ Q,eval Q D ≠ 0) :
    ∃ Q : Fin (upperEndpoint m) → Forms K m 2,
      eval (fun i => finiteEquiv (Q i.1) i.2) D ≠ 0 ∧
      ∃ Z : (d : ConvolutionExpansionOpen.Dimensions m upper) → Fin (slices m upper d.val) → Rows K m 3,
        ∀ d : ConvolutionExpansionOpen.Dimensions m upper,∀ lam : Fin (RowCount m 3) → K,
          d.val+mixedCount m upper ≤ finrank K (LinearMap.ker
            (relationMap RowMultiplicationCoordinates.coordinate lam)) →
          (∀ j f,covector lam (RowMultiplicationCoordinates.coordinate f (rowFiniteEquiv (g j)))=0) →
          (∀ i v,covector lam (RowMultiplicationCoordinates.coordinate (finiteEquiv (Q i)) v)=0) →
          (∀ j,covector lam (rowFiniteEquiv (Z d j))=0) → lam=0 := by
  classical
  let a := totalA m (mixedCount m upper)
  have ha : finrank K (Source g)=a := by
    rw [ExpansionCommonOpen.linear_quotient_dimension g hg]
    have hc := ConvolutionAllRange.endpoint_columns_range m hm upper
    exact (totalA_eq m _ hc.1 hc.2).symm
  let eV : Source g ≃ₗ[K] (Fin a → K) := LinearEquiv.ofFinrankEq _ _ (by simpa using ha)
  let eW := coordinates K (Target g)
  let V := ExpansionClosedSlices.Input K a (FormCount m 2) (finrank K (Target g)) (upperEndpoint m) (slices m upper)
  obtain ⟨P,hP,hgood⟩ := principal_open_actual_slices m hm upper g hg E hE hexp eV eW
  let childProjection : V →ₗ[K] (Fin (upperEndpoint m) × Fin (FormCount m 2) → K) :=
    { toFun := fun x i => x.1 i.1 i.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let f := childProjection.comp (coordinates K V).symm.toLinearMap
  let D' := MiddleCoordinates.substituteLinear f D
  have hDn : D' ≠ 0 := by
    obtain ⟨Q,hQ⟩ := hD
    let x : V := (fun i j => Q (i,j),0)
    have hx : eval (coordinates K V x) D' ≠ 0 := by
      simpa only [D',MiddleCoordinates.eval_substituteLinear,f,LinearMap.comp_apply,
        LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,childProjection,LinearMap.coe_mk,
        AddHom.coe_mk,x] using hQ
    intro hz
    exact hx (by rw [hz,map_zero])
  have hPn : P ≠ 0 := by
    obtain ⟨x,hx⟩ := hP
    intro hz
    exact hx (by rw [hz,map_zero])
  obtain ⟨z,hz⟩ := PolynomialImageAvoidance.exists_eval_ne_zero (mul_ne_zero hPn hDn)
  rw [map_mul,mul_ne_zero_iff] at hz
  let x : V := (coordinates K V).symm z
  have hx : eval (coordinates K V x) P ≠ 0 := by simpa only [x,LinearEquiv.apply_symm_apply] using hz.1
  obtain ⟨Z,hZ⟩ := lift_closed_slices_coordinates g hg eV eW (slices m upper) x (hgood x hx)
  refine ⟨fun i => finiteEquiv.symm (x.1 i),?_,Z,?_⟩
  · have hh : eval (childProjection x) D ≠ 0 := by
      simpa only [D',MiddleCoordinates.eval_substituteLinear,f,LinearMap.comp_apply,LinearEquiv.coe_coe,x] using hz.2
    simpa only [LinearEquiv.apply_symm_apply,childProjection,LinearMap.coe_mk,AddHom.coe_mk] using hh
  · simpa only [LinearEquiv.apply_symm_apply] using hZ

/-- The slice budget is exactly the motion budget with an integer target
surplus; this is the form consumed by the actual ambient motion matrices. -/
theorem slices_eq (m : ℕ) (upper : Bool) (d : ℕ) :
    slices m upper d = (2*m+2*mixedCount m upper-4*d)+
      (correctionCount m upper-mixedCount m upper*d)+
      (Counts.j m (upperEndpoint m) (mixedCount m upper)-
        ((2*m+2*mixedCount m upper:ℕ):ℤ)-correctionCount m upper).toNat := by
  unfold slices ExpansionClosedSlices.sliceCount
  congr 1
  omega

end Quartic.ActualExpansionSlices
