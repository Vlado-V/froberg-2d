module

public import Quartic.AmbientCovectorTransport
public import Quartic.AmbientCovectorSpreading
public import Quartic.EndpointF13AllRange

@[expose] public section

/-! Common actual block coefficients for every small-range closed covector threshold. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Quartic.SmallCovectorCommonOpen
open Module MvPolynomial UniformEndpoint ProfileCertificate ConvolutionClosedSlices
open RowMultiplicationCoordinates HomogeneousCoefficientCoordinates
open BilinearCoefficientKernel BilinearCovectorCharts
variable {K : Type*} [Field K] {M m c q : ℕ} {upper : Bool}

abbrev Threshold := ConvolutionSharedSlices.Threshold
abbrev SliceIndex (M : ℕ) (upper : Bool) (m : ℕ) :=
  (d : Threshold M upper) × (Fin (sliceCount M upper d.val) × RowIndex m 3)
abbrev ParameterIndex (M : ℕ) (upper : Bool) (m c q : ℕ) :=
  AugmentedGeneric.ParameterIndex m c q ⊕ SliceIndex M upper m

def baseProjection : (ParameterIndex M upper m c q → K) →ₗ[K]
    (AugmentedGeneric.ParameterIndex m c q → K) :=
  LinearMap.pi (fun i => LinearMap.proj (Sum.inl i))

def sliceColumn (d : Threshold M upper) (j : Fin (sliceCount M upper d.val)) :
    (ParameterIndex M upper m c q → K) →ₗ[K] Rows K m 3 :=
  rowEquiv.symm.toLinearMap.comp (LinearMap.pi (fun i => LinearMap.proj (Sum.inr ⟨d,(j,i)⟩)))

def coefficientSlices (p : ParameterIndex M upper m c q → K)
    (d : Threshold M upper) : Fin (sliceCount M upper d.val) → Rows K m 3 :=
  fun j => sliceColumn d j p

def encode (b : AugmentedGeneric.ParameterIndex m c q → K)
    (Z : (d : Threshold M upper) → Fin (sliceCount M upper d.val) → Rows K m 3) :
    ParameterIndex M upper m c q → K :=
  Sum.elim b (fun i => rowEquiv (Z i.1 i.2.1) i.2.2)

@[simp] theorem baseProjection_encode (b : AugmentedGeneric.ParameterIndex m c q → K)
    (Z : (d : Threshold M upper) → Fin (sliceCount M upper d.val) → Rows K m 3) :
    baseProjection (encode b Z) = b := rfl

@[simp] theorem coefficientSlices_encode (b : AugmentedGeneric.ParameterIndex m c q → K)
    (Z : (d : Threshold M upper) → Fin (sliceCount M upper d.val) → Rows K m 3)
    (d : Threshold M upper) (j : Fin (sliceCount M upper d.val)) :
    coefficientSlices (encode b Z) d j = Z d j := by
  change rowEquiv.symm (rowEquiv (Z d j)) = Z d j
  exact rowEquiv.symm_apply_apply (Z d j)

/-- The same E and Q occur in every threshold. -/
def ClosedConditions (p : ParameterIndex M upper m c q → K) : Prop :=
  ∀ d : Threshold M upper,∀ ell : Fin (RowCount m 3) → K,
    d.val+c ≤ finrank K (LinearMap.ker (relationMap coordinate ell)) →
    (∀ j f,covector ell (coordinate f
      (rowFiniteEquiv (AugmentedGeneric.coefficientMixed (baseProjection p) j)))=0) →
    (∀ i v,covector ell (coordinate
      (finiteEquiv (AugmentedGeneric.coefficientChild (baseProjection p) i)) v)=0) →
    (∀ j,covector ell (rowFiniteEquiv (coefficientSlices p d j))=0) → ell=0

/-- A finite product retains all closed sections at the same witness. -/
theorem principal_open_of_witness [IsAlgClosed K]
    (hd : ∀ d : Threshold M upper,d.val+c ≤ RowCount m 1)
    (p₀ : ParameterIndex M upper m c q → K) (hwitness : ClosedConditions p₀) :
    ∃ D : MvPolynomial (ParameterIndex M upper m c q) K,
      eval p₀ D ≠ 0 ∧ ∀ p,eval p D ≠ 0 → ClosedConditions p := by
  classical
  have hopen : ∀ d : Threshold M upper,∃ D : MvPolynomial (ParameterIndex M upper m c q) K,
      eval p₀ D ≠ 0 ∧ ∀ p,eval p D ≠ 0 →
        ∀ ell : Fin (RowCount m 3) → K,
          d.val+c ≤ finrank K (LinearMap.ker (relationMap coordinate ell)) →
          (∀ j f,covector ell (coordinate f
            (rowFiniteEquiv (AugmentedGeneric.coefficientMixed (baseProjection p) j)))=0) →
          (∀ i v,covector ell (coordinate
            (finiteEquiv (AugmentedGeneric.coefficientChild (baseProjection p) i)) v)=0) →
          (∀ j,covector ell (rowFiniteEquiv (coefficientSlices p d j))=0) → ell=0 := by
    intro d
    apply AmbientCovectorSpreading.principal_open_closed_of_witness (K := K) (I := ParameterIndex M upper m c q) coordinate
      (fun p j => rowFiniteEquiv (AugmentedGeneric.coefficientMixed (baseProjection p) j))
      (fun p i => finiteEquiv (AugmentedGeneric.coefficientChild (baseProjection p) i))
      (fun p j => rowFiniteEquiv (coefficientSlices p d j))
    · intro j v
      exact isPolynomialFamily_linear (K := K) ((LinearMap.proj v).comp
        (rowFiniteEquiv.toLinearMap.comp ((LinearMap.proj j).comp
          (AugmentedGeneric.coefficientMixed.comp baseProjection))))
    · intro i f
      exact isPolynomialFamily_linear (K := K) ((LinearMap.proj f).comp
        (finiteEquiv.toLinearMap.comp ((LinearMap.proj i).comp
          (AugmentedGeneric.coefficientChild.comp baseProjection))))
    · intro j k
      exact isPolynomialFamily_linear (K := K) ((LinearMap.proj k).comp
        (rowFiniteEquiv.toLinearMap.comp (sliceColumn d j)))
    · exact hd d
    · exact hwitness d
  choose D hD hgood using hopen
  refine ⟨∏ d,D d,?_,?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun d _ => hD d)
  · intro p hp d
    have hd' : eval p (D d) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp (by simpa only [map_prod] using hp) d (Finset.mem_univ d)
    exact hgood d p hd'

include K in
theorem rowCount_one (m : ℕ) : RowCount m 1 = 3*m := by
  have h := (rowFiniteEquiv (K := K) (m := m) (d := 1)).finrank_eq
  rw [Module.finrank_fin_fun] at h
  have hdim : finrank K (Rows K m 1)=3*m := by
    simp [Rows,Module.finrank_pi_fintype,finrank_forms]
  exact h.symm.trans hdim

/-- No geometric witness or compatibility premise remains in this proposition. -/
def ClosedOpen (M : ℕ) (upper : Bool) (m c q : ℕ) : Prop :=
  ∃ D : MvPolynomial (ParameterIndex M upper m c q) K,
    (∃ p,eval p D ≠ 0) ∧ ∀ p,eval p D ≠ 0 → ClosedConditions p

theorem convolution_open [IsAlgClosed K] (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40)
    (upper : Bool) : ClosedOpen (K := K) m upper m (mixedCount m upper) (upperEndpoint m) := by
  let t := coreP (mixedCount m upper)+1
  let w := freeW m (mixedCount m upper)
  let q := upperEndpoint m
  have hc := ConvolutionAllRange.endpoint_columns_range m hmlo upper
  have ht : 2 ≤ t := by dsimp [t]; unfold coreP; omega
  have hvars : t+w=m := ConvolutionAllRange.endpoint_variable_count m hmlo upper
  have hcols : t+2=mixedCount m upper := by dsimp [t]; unfold coreP; omega
  obtain ⟨Q,Z,hwitness⟩ := ConvolutionAmbientSlices.exists_all_coordinate_sections
    (K := K) m hmlo hmhi upper ht
  let b := AugmentedGeneric.encode (GenericF13Endpoint.convolutionMixed K t w)
    (fun i => finiteEquiv.symm (Q i)) (0 : Fin 4 → Forms K (t+w) 2)
  let p₀ : ParameterIndex m upper (t+w) (t+2) q → K :=
    encode b (fun d j => rowFiniteEquiv.symm (Z d j))
  have hempty : ClosedConditions p₀ := by
    intro d ell hker hE hQ hZ
    apply hwitness d ell hker
    · intro f j
      simpa only [p₀,b,baseProjection_encode,AugmentedGeneric.coefficientMixed_encode] using hE j f
    · simpa only [p₀,b,baseProjection_encode,AugmentedGeneric.coefficientChild_encode,
        LinearEquiv.apply_symm_apply] using hQ
    · simpa only [p₀,coefficientSlices_encode,LinearEquiv.apply_symm_apply] using hZ
  have hd : ∀ d : Threshold m upper,d.val+(t+2) ≤ RowCount (t+w) 1 := by
    intro d
    rw [rowCount_one (K := K),hvars,hcols]
    have hh := d.isLt
    have he := totalA_eq m _ hc.1 hc.2
    omega
  obtain ⟨D,hD,hgood⟩ := principal_open_of_witness hd p₀ hempty
  have hh : ClosedOpen (K := K) m upper (t+w) (t+2) q := ⟨D,⟨p₀,hD⟩,hgood⟩
  simpa only [hvars,hcols,q] using hh

/-- The closed covector sections and every checked block/F13/cubic condition
hold on one nonempty open, using identical mixed and child coefficients. -/
theorem common_open [IsAlgClosed K] (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40)
    (upper : Bool) (h2 : (2 : K) ≠ 0) :
    ∃ D : MvPolynomial (ParameterIndex m upper m (mixedCount m upper) (upperEndpoint m)) K,
      (∃ p,eval p D ≠ 0) ∧ ∀ p,eval p D ≠ 0 →
        SimultaneousBlockConditions.BlockConditions (baseProjection p) ∧
        GenericF13.Conditions (AugmentedGeneric.coefficientMixed (baseProjection p))
          (AugmentedGeneric.coefficientChild (baseProjection p)) ∧
        finrank K (CubicGeneric.CubicQuotient (AugmentedGeneric.coefficientChild (baseProjection p))) =
          (m+2).choose 3-m*upperEndpoint m ∧ ClosedConditions p := by
  classical
  obtain ⟨A,⟨a,ha⟩,hA⟩ := convolution_open (K := K) m hmlo hmhi upper
  obtain ⟨B,⟨b,hb⟩,hB⟩ := EndpointF13AllRange.generic_endpoint_conditions (K := K) m hmlo upper h2
  let B' : MvPolynomial (ParameterIndex m upper m (mixedCount m upper) (upperEndpoint m)) K :=
    rename Sum.inl B
  have hA0 : A ≠ 0 := by intro h; simp [h] at ha
  have hB0 : B' ≠ 0 := by
    have he : eval (encode b 0) B' ≠ 0 := by
      simpa [B',eval_rename,encode,Function.comp_def] using hb
    intro h
    simp only [h,map_zero,ne_eq,not_true_eq_false] at he
  obtain ⟨p₀,hp₀⟩ := PolynomialImageAvoidance.exists_eval_ne_zero (mul_ne_zero hA0 hB0)
  refine ⟨A*B',⟨p₀,hp₀⟩,?_⟩
  intro p hp
  rw [map_mul,mul_ne_zero_iff] at hp
  have hb' : eval (baseProjection p) B ≠ 0 := by
    change eval (fun i => p (Sum.inl i)) B ≠ 0
    simpa only [B',eval_rename,Function.comp_def] using hp.2
  obtain ⟨hblock,hf13,hcubic⟩ := hB (baseProjection p) hb'
  exact ⟨hblock,hf13,hcubic,hA p hp.1⟩

end Quartic.SmallCovectorCommonOpen
