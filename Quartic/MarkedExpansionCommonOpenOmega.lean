module

public import Quartic.MarkedConvolutionExpansionOpen
public import Quartic.EndpointF13AllRangeOmega
public import Quartic.FixedBlockChildOpen

@[expose] public section

/-! Finite marked expansion with all original coefficient opens retained. -/
noncomputable section
namespace Quartic.MarkedExpansionCommonOpenOmega
open Module MvPolynomial RowMultiplicationCoordinates RowExpansionOpen
open UniformEndpoint ProfileCertificate
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]

def ExpansionOpen (M : ℕ) (upper : Bool) (m c q : ℕ) : Prop :=
  ∃ E : MarkedConvolutionExpansionOpen.Dimensions M upper → ℕ,
    MarkedConvolutionExpansionOpen.Thresholds M upper E ∧
    ∃ D : MvPolynomial (AugmentedGeneric.ParameterIndex m c q) K,
      (∃ p, eval p D ≠ 0) ∧ ∀ p, eval p D ≠ 0 →
        ∀ d : MarkedConvolutionExpansionOpen.Dimensions M upper,
          RowExpansionOpen.Expands (AugmentedGeneric.coefficientMixed p)
            (d.val+mixedCount M upper) (E d+mixedCount M upper*(M+1).choose 2)

include L in
theorem expansion_augmented (m : ℕ) (hm : 41 ≤ m) (hmhi : m ≤ 319)
    (hpositive : 0 < Counts.chi (m + 3) (upperEndpoint m + mixedCount m false + 4)) :
    ExpansionOpen (K := K) m false m (mixedCount m false) (upperEndpoint m) := by
  let t := coreP (mixedCount m false)+1
  let w := freeW m (mixedCount m false)
  let q := upperEndpoint m
  let g := fun p : AugmentedGeneric.ParameterIndex (t+w) (t+2) q → K =>
    AugmentedGeneric.coefficientMixed p
  let p₀ := AugmentedGeneric.encode (GenericF13Endpoint.convolutionMixed K t w)
    (0 : Fin q → Forms K (t+w) 2) 0
  have hp₀ : g p₀ = GenericF13Endpoint.convolutionMixed K t w :=
    AugmentedGeneric.coefficientMixed_encode _ _ _
  have hg : ∀ j, IsPolynomialFamily (fun p => g p j) :=
    fun j => isPolynomialFamily_linear ((LinearMap.proj j).comp AugmentedGeneric.coefficientMixed)
  obtain ⟨E,hE,D,hD,hgood⟩ := MarkedConvolutionExpansionOpen.principal_open_family
    (L := L) m hm hmhi hpositive g hg p₀ hp₀
  have hh : ExpansionOpen (K := K) m false (t+w) (t+2) q :=
    ⟨E,hE,D,⟨p₀,hD⟩,hgood⟩
  have hvars : t+w=m := ConvolutionOuterGeneric.endpoint_variable_count m hm false
  have hc := ConvolutionOuterGeneric.endpoint_columns_range m hm false
  have hcols : t+2=mixedCount m false := by dsimp [t]; unfold coreP; omega
  simpa only [hvars,hcols,q] using hh

include L in
theorem common_open [Infinite K] (ω : K) (m : ℕ) (hm : 41 ≤ m) (hmhi : m ≤ 319)
    (hpositive : 0 < Counts.chi (m + 3) (upperEndpoint m + mixedCount m false + 4)) (hω : ω ≠ 0) (hω1 : ω ≠ -1) :
    ∃ E : MarkedConvolutionExpansionOpen.Dimensions m false → ℕ,
      MarkedConvolutionExpansionOpen.Thresholds m false E ∧
      ∃ D : MvPolynomial (AugmentedGeneric.ParameterIndex m (mixedCount m false) (upperEndpoint m)) K,
        (∃ p, eval p D ≠ 0) ∧ ∀ p, eval p D ≠ 0 →
          SimultaneousBlockConditionsOmega.BlockConditions ω p ∧
          GenericF13.Conditions (AugmentedGeneric.coefficientMixed p) (AugmentedGeneric.coefficientChild p) ∧
          finrank K (CubicGeneric.CubicQuotient (AugmentedGeneric.coefficientChild p)) =
            (m+2).choose 3-m*upperEndpoint m ∧
          ∀ d : MarkedConvolutionExpansionOpen.Dimensions m false,
            RowExpansionOpen.Expands (AugmentedGeneric.coefficientMixed p)
              (d.val+mixedCount m false) (E d+mixedCount m false*(m+1).choose 2) := by
  classical
  obtain ⟨E,hE,A,⟨a,ha⟩,hA⟩ := expansion_augmented (K := K) (L := L) m hm hmhi hpositive
  obtain ⟨B,⟨b,hb⟩,hB⟩ := EndpointF13AllRangeOmega.generic_endpoint_conditions (K := K) ω m (by omega) false hω hω1
  have hA0 : A ≠ 0 := by intro h; simp [h] at ha
  have hB0 : B ≠ 0 := by intro h; simp [h] at hb
  obtain ⟨p₀,hp₀⟩ := nonempty_principal_intersection
    (![A,B] : Fin 2 → MvPolynomial
      (AugmentedGeneric.ParameterIndex m (mixedCount m false) (upperEndpoint m)) K)
    (by intro i; fin_cases i <;> assumption)
  refine ⟨E,hE,A*B,⟨p₀,?_⟩,?_⟩
  · rw [map_mul]
    exact mul_ne_zero (hp₀ 0) (hp₀ 1)
  · intro p hp
    rw [map_mul,mul_ne_zero_iff] at hp
    obtain ⟨hb,hf,hc⟩ := hB p hp.2
    exact ⟨hb,hf,hc,hA p hp.1⟩


include L in
/-- Fix the mixed family and pure motions at an actual common-open point.
The remaining child-coordinate open preserves every required condition. -/
theorem exists_fixed_open [Infinite K] (ω : K) (m : ℕ) (hm : 41 ≤ m) (hmhi : m ≤ 319)
    (hpositive : 0 < Counts.chi (m + 3) (upperEndpoint m + mixedCount m false + 4))
    (hω : ω ≠ 0) (hω1 : ω ≠ -1) :
    ∃ g : Fin (mixedCount m false) → Rows K m 1,
    ∃ r : Fin 4 → Forms K m 2,
    ∃ E : MarkedConvolutionExpansionOpen.Dimensions m false → ℕ,
      MarkedConvolutionExpansionOpen.Thresholds m false E ∧ LinearIndependent K g ∧
      (∀ d : MarkedConvolutionExpansionOpen.Dimensions m false, RowExpansionOpen.Expands g
        (d.val+mixedCount m false) (E d+mixedCount m false*(m+1).choose 2)) ∧
      ∃ D : MvPolynomial (FixedBlockChildOpen.ChildIndex m (upperEndpoint m)) K,
        (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
          SimultaneousBlockConditionsOmega.BlockConditions ω
            (AugmentedGeneric.encode g (FixedBlockChildOpen.decode a) r) ∧
          GenericF13.Conditions g (FixedBlockChildOpen.decode a) ∧
          finrank K (CubicGeneric.CubicQuotient (FixedBlockChildOpen.decode a)) =
            (m+2).choose 3-m*upperEndpoint m := by
  classical
  obtain ⟨E,hE,D,⟨p₀,hp₀⟩,hD⟩ := common_open (K := K) (L := L) ω m hm hmhi hpositive hω hω1
  let g := AugmentedGeneric.coefficientMixed p₀
  let r := AugmentedGeneric.coefficientMotions p₀
  obtain ⟨hblock₀,hf₀,hc₀,hexp⟩ := hD p₀ hp₀
  let B := FixedBlockChildOpen.pullback g r D
  have hB : ∃ a, eval a B ≠ 0 := by
    refine ⟨FixedBlockChildOpen.encodeChild (AugmentedGeneric.coefficientChild p₀), ?_⟩
    simpa only [B,FixedBlockChildOpen.eval_pullback,FixedBlockChildOpen.decode_encode,
      g,r,FixedBlockChildOpen.encode_recover] using hp₀
  refine ⟨g,r,E,hE,hblock₀.1.1,hexp,B,hB,?_⟩
  intro a ha
  have hp : eval (AugmentedGeneric.encode g (FixedBlockChildOpen.decode a) r) D ≠ 0 := by
    simpa only [B,FixedBlockChildOpen.eval_pullback] using ha
  obtain ⟨hblock,hf,hc,_⟩ := hD _ hp
  exact ⟨hblock,by simpa only [AugmentedGeneric.coefficientMixed_encode,
      AugmentedGeneric.coefficientChild_encode] using hf,
    by
      have he := congrArg (fun h : Fin (upperEndpoint m) → Forms K m 2 =>
        finrank K (CubicGeneric.CubicQuotient h))
        (AugmentedGeneric.coefficientChild_encode g (FixedBlockChildOpen.decode a) r)
      exact he.symm.trans hc⟩


include L in
/-- Any prescribed full-parameter open is intersected before the mixed family
and pure motions are fixed. Its certificate is retained on the child fiber. -/
theorem exists_fixed_open_with [Infinite K] (ω : K) (m : ℕ) (hm : 41 ≤ m) (hmhi : m ≤ 319)
    (hpositive : 0 < Counts.chi (m + 3) (upperEndpoint m + mixedCount m false + 4))
    (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (A : MvPolynomial (AugmentedGeneric.ParameterIndex m (mixedCount m false) (upperEndpoint m)) K)
    (hA : ∃ p, eval p A ≠ 0) :
    ∃ g : Fin (mixedCount m false) → Rows K m 1,
    ∃ r : Fin 4 → Forms K m 2,
    ∃ E : MarkedConvolutionExpansionOpen.Dimensions m false → ℕ,
      MarkedConvolutionExpansionOpen.Thresholds m false E ∧ LinearIndependent K g ∧
      (∀ d : MarkedConvolutionExpansionOpen.Dimensions m false, RowExpansionOpen.Expands g
        (d.val+mixedCount m false) (E d+mixedCount m false*(m+1).choose 2)) ∧
      ∃ D : MvPolynomial (FixedBlockChildOpen.ChildIndex m (upperEndpoint m)) K,
        (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
          SimultaneousBlockConditionsOmega.BlockConditions ω
            (AugmentedGeneric.encode g (FixedBlockChildOpen.decode a) r) ∧
          GenericF13.Conditions g (FixedBlockChildOpen.decode a) ∧
          finrank K (CubicGeneric.CubicQuotient (FixedBlockChildOpen.decode a)) =
            (m+2).choose 3-m*upperEndpoint m ∧
          eval (AugmentedGeneric.encode g (FixedBlockChildOpen.decode a) r) A ≠ 0 := by
  classical
  obtain ⟨E,hE,D,⟨p,hp⟩,hD⟩ := common_open (K := K) (L := L) ω m hm hmhi hpositive hω hω1
  have hDn : D ≠ 0 := by intro h; exact hp (by rw [h,map_zero])
  have hAn : A ≠ 0 := by
    obtain ⟨a,ha⟩ := hA
    intro h; exact ha (by rw [h,map_zero])
  obtain ⟨p₀,hp₀⟩ := PolynomialImageAvoidance.exists_eval_ne_zero (mul_ne_zero hDn hAn)
  have hpD : eval p₀ D ≠ 0 := (mul_ne_zero_iff.mp (by simpa only [map_mul] using hp₀)).1
  let g := AugmentedGeneric.coefficientMixed p₀
  let r := AugmentedGeneric.coefficientMotions p₀
  obtain ⟨hblock₀,hf₀,hc₀,hexp⟩ := hD p₀ hpD
  let B := FixedBlockChildOpen.pullback g r (D*A)
  have hB : ∃ a, eval a B ≠ 0 := by
    refine ⟨FixedBlockChildOpen.encodeChild (AugmentedGeneric.coefficientChild p₀), ?_⟩
    simpa only [B,FixedBlockChildOpen.eval_pullback,FixedBlockChildOpen.decode_encode,
      g,r,FixedBlockChildOpen.encode_recover] using hp₀
  refine ⟨g,r,E,hE,hblock₀.1.1,hexp,B,hB,?_⟩
  intro a ha
  have hp : eval (AugmentedGeneric.encode g (FixedBlockChildOpen.decode a) r) (D*A) ≠ 0 := by
    simpa only [B,FixedBlockChildOpen.eval_pullback] using ha
  rw [map_mul,mul_ne_zero_iff] at hp
  obtain ⟨hblock,hf,hc,_⟩ := hD _ hp.1
  refine ⟨hblock,?_,?_,hp.2⟩
  · simpa only [AugmentedGeneric.coefficientMixed_encode,
      AugmentedGeneric.coefficientChild_encode] using hf
  · have he := congrArg (fun h : Fin (upperEndpoint m) → Forms K m 2 =>
        finrank K (CubicGeneric.CubicQuotient h))
        (AugmentedGeneric.coefficientChild_encode g (FixedBlockChildOpen.decode a) r)
    exact he.symm.trans hc

end Quartic.MarkedExpansionCommonOpenOmega
