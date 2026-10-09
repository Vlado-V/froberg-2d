module

public import Quartic.ActualExpansionSlices
public import Quartic.MarkedConvolutionExpansionOpen
public import Quartic.FixedBlockChildOpen
public import Froberg.FreezeParameters

@[expose] public section

/-! Actual covector slices with the additional marked correction column. -/
noncomputable section
namespace Quartic.MarkedActualExpansionSlices
open Module MvPolynomial RowMultiplicationCoordinates HomogeneousCoefficientCoordinates
open UniformEndpoint ProfileCertificate PolynomialBilinearCoordinates
open BilinearCovectorCharts BilinearCoefficientKernel ConvolutionClosedSlices
open ActualExpansionSlices
variable {K : Type*} [Field K] {m c : ℕ}
set_option maxHeartbeats 1500000

def correctionCount (m : ℕ) (upper : Bool) : ℕ :=
  (Counts.H m (upperEndpoint m) (mixedCount m upper)+4+Counts.delta m (upperEndpoint m)).toNat

def slices (m : ℕ) (upper : Bool) : ℕ → ℕ :=
  ExpansionClosedSlices.sliceCount (2*m+2*mixedCount m upper) (correctionCount m upper)
    (mixedCount m upper) (Counts.j m (upperEndpoint m) (mixedCount m upper)).toNat

theorem correctionCount_cast (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    (correctionCount m upper:ℤ)=Counts.H m (upperEndpoint m) (mixedCount m upper)+4+
      Counts.delta m (upperEndpoint m) := by
  have h := dimension_signs m hm upper
  exact Int.toNat_of_nonneg (by omega)

/-- The attained ambient expansion bounds become the scalar incidence
bounds for every actual quotient subspace. -/
theorem actual_scalar_bounds (m : ℕ) (hm : 28 ≤ m) (upper : Bool)
    (g : Fin (mixedCount m upper) → Rows K m 1) (hg : LinearIndependent K g)
    (E : MarkedConvolutionExpansionOpen.Dimensions m upper → ℕ)
    (hE : MarkedConvolutionExpansionOpen.Thresholds m upper E)
    (hexp : ∀ d : MarkedConvolutionExpansionOpen.Dimensions m upper,RowExpansionOpen.Expands g
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
  let d : MarkedConvolutionExpansionOpen.Dimensions m upper := ⟨finrank K S,by omega⟩
  have hz := hexp 0
  simp only [Fin.val_zero,zero_add] at hz
  have himage : E d ≤ finrank K (BilinearImage.image (actualMu g eV eW) S) := by
    rw [ActualExpansionSlices.actual_image_finrank]
    apply ExpansionCommonOpen.quotient_expansion g hg (E 0) hz (hexp d)
    exact eV.symm.finrank_map_eq S
  have hb := ((hE d).2 hlo hhi).mono (E' := (finrank K (BilinearImage.image (actualMu g eV eW) S):ℝ)) (by exact_mod_cast himage)
  have hcounts := HullCertificate.scalars_original_counts m (upperEndpoint m) (mixedCount m upper)
  have hsur := (surplus_cast m hm upper g hg (E 0) hz).2
  have hsurR : ((finrank K (Target g)-upperEndpoint m*totalA m (mixedCount m upper):ℕ):ℝ)=
      (Counts.j m (upperEndpoint m) (mixedCount m upper):ℝ) := by exact_mod_cast hsur
  have hcorR : (correctionCount m upper:ℝ)=(Counts.H m (upperEndpoint m) (mixedCount m upper):ℝ)+4+
      (Counts.delta m (upperEndpoint m):ℝ) := by exact_mod_cast correctionCount_cast m hm upper
  have htotR : ((Counts.hTotal m (upperEndpoint m) (mixedCount m upper):ℝ)+1)=
      ((2*m+2*mixedCount m upper+correctionCount m upper:ℕ):ℝ) := by
    unfold Counts.hTotal Counts.k31
    push_cast
    rw [hcorR]
    ring
  have hs := hb.2
  simp only [HullCertificate.codimension,HullCertificate.target,HullCertificate.markedScalars] at hs
  rw [hcounts.1,hcounts.2.1,hcounts.2.2.1,hcounts.2.2.2] at hs
  simp only [HullCertificate.scalars,Counts.k31,Int.cast_max,Int.cast_add,Int.cast_sub,
    Int.cast_mul,Int.cast_natCast,Int.cast_zero,Int.cast_one,Int.cast_ofNat,d] at hs
  dsimp only
  rw [hsurR]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,hcorR,UniformScalar.codimensionR]
  rw [htotR] at hs
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,hcorR] at hs
  have hmark : (Counts.H m (upperEndpoint m) (mixedCount m upper):ℝ)+3+
      (Counts.delta m (upperEndpoint m):ℝ)+1 =
      (Counts.H m (upperEndpoint m) (mixedCount m upper):ℝ)+4+
        (Counts.delta m (upperEndpoint m):ℝ) := by ring
  simpa only [hmark] using hs

/-- On an actual expanded mixed presentation, one genuine principal open
chooses a shared child tuple and all closed-threshold slices. -/
theorem principal_open_actual_slices [Infinite K] (m : ℕ) (hm : 28 ≤ m) (upper : Bool)
    (g : Fin (mixedCount m upper) → Rows K m 1) (hg : LinearIndependent K g)
    (E : MarkedConvolutionExpansionOpen.Dimensions m upper → ℕ)
    (hE : MarkedConvolutionExpansionOpen.Thresholds m upper E)
    (hexp : ∀ d : MarkedConvolutionExpansionOpen.Dimensions m upper,RowExpansionOpen.Expands g
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
        ∀ d : MarkedConvolutionExpansionOpen.Dimensions m upper,∀ ell : Fin (finrank K (Target g)) → K,
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

/-- An arbitrary additional child-coefficient principal open can be
intersected without changing the fixed mixed presentation or any threshold. -/
theorem exists_ambient_slices_in_open [Infinite K] (m : ℕ) (hm : 28 ≤ m) (upper : Bool)
    (g : Fin (mixedCount m upper) → Rows K m 1) (hg : LinearIndependent K g)
    (E : MarkedConvolutionExpansionOpen.Dimensions m upper → ℕ)
    (hE : MarkedConvolutionExpansionOpen.Thresholds m upper E)
    (hexp : ∀ d : MarkedConvolutionExpansionOpen.Dimensions m upper,RowExpansionOpen.Expands g
      (d.val+mixedCount m upper) (E d+mixedCount m upper*(m+1).choose 2))
    (D : MvPolynomial (Fin (upperEndpoint m) × Fin (FormCount m 2)) K)
    (hD : ∃ Q,eval Q D ≠ 0) :
    ∃ Q : Fin (upperEndpoint m) → Forms K m 2,
      eval (fun i => finiteEquiv (Q i.1) i.2) D ≠ 0 ∧
      ∃ Z : (d : MarkedConvolutionExpansionOpen.Dimensions m upper) → Fin (slices m upper d.val) → Rows K m 3,
        ∀ d : MarkedConvolutionExpansionOpen.Dimensions m upper,∀ lam : Fin (RowCount m 3) → K,
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

end Quartic.MarkedActualExpansionSlices
