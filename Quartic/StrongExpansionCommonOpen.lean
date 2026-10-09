module

public import Quartic.StrongExpansionOpen
public import Quartic.ExpansionCommonOpen
public import Quartic.FixedBlockChildOpen

@[expose] public section

/-! A common actual parameter open retains the full convolution surplus.
Fixing the mixed family leaves an actual nonempty child-coordinate open;
no generic endpoint conclusion for the child is assumed. -/
noncomputable section
namespace Quartic.StrongExpansionCommonOpen
open Module MvPolynomial RowMultiplicationCoordinates RowExpansionOpen
open UniformEndpoint ProfileCertificate
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
def ExpansionOpen (M : ℕ) (upper : Bool) (m c q : ℕ) : Prop :=
  ∃ E : StrongExpansionOpen.Dimensions M upper → ℕ,
    StrongExpansionOpen.Thresholds M upper E ∧
    ∃ D : MvPolynomial (AugmentedGeneric.ParameterIndex m c q) K,
      (∃ p, eval p D ≠ 0) ∧ ∀ p, eval p D ≠ 0 →
        ∀ d : StrongExpansionOpen.Dimensions M upper,
          RowExpansionOpen.Expands (AugmentedGeneric.coefficientMixed p)
            (d.val+mixedCount M upper) (E d+mixedCount M upper*(M+1).choose 2)

include L in
theorem expansion_augmented (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    ExpansionOpen (K := K) m upper m (mixedCount m upper) (upperEndpoint m) := by
  let t := coreP (mixedCount m upper)+1
  let w := freeW m (mixedCount m upper)
  let q := upperEndpoint m
  let g := fun p : AugmentedGeneric.ParameterIndex (t+w) (t+2) q → K =>
    AugmentedGeneric.coefficientMixed p
  let p₀ := AugmentedGeneric.encode (GenericF13Endpoint.convolutionMixed K t w)
    (0 : Fin q → Forms K (t+w) 2) 0
  have hp₀ : g p₀ = GenericF13Endpoint.convolutionMixed K t w :=
    AugmentedGeneric.coefficientMixed_encode _ _ _
  have hg : ∀ j, IsPolynomialFamily (fun p => g p j) :=
    fun j => isPolynomialFamily_linear ((LinearMap.proj j).comp AugmentedGeneric.coefficientMixed)
  obtain ⟨E,hE,D,hD,hgood⟩ := StrongExpansionOpen.principal_open_family
    (L := L) m hm upper g hg p₀ hp₀
  have hh : ExpansionOpen (K := K) m upper (t+w) (t+2) q :=
    ⟨E,hE,D,⟨p₀,hD⟩,hgood⟩
  have hvars : t+w=m := ConvolutionOuterGeneric.endpoint_variable_count m (by omega) upper
  have hc := ConvolutionOuterGeneric.endpoint_columns_range m (by omega) upper
  have hcols : t+2=mixedCount m upper := by dsimp [t]; unfold coreP; omega
  simpa only [hvars,hcols,q] using hh

include L in
theorem common_open [Infinite K] (m : ℕ) (hm : 320 ≤ m) (upper : Bool) (h2 : (2 : K) ≠ 0) :
    ∃ E : StrongExpansionOpen.Dimensions m upper → ℕ,
      StrongExpansionOpen.Thresholds m upper E ∧
      ∃ D : MvPolynomial (AugmentedGeneric.ParameterIndex m (mixedCount m upper) (upperEndpoint m)) K,
        (∃ p, eval p D ≠ 0) ∧ ∀ p, eval p D ≠ 0 →
          SimultaneousBlockConditions.BlockConditions p ∧
          GenericF13.Conditions (AugmentedGeneric.coefficientMixed p) (AugmentedGeneric.coefficientChild p) ∧
          finrank K (CubicGeneric.CubicQuotient (AugmentedGeneric.coefficientChild p)) =
            (m+2).choose 3-m*upperEndpoint m ∧
          ∀ d : StrongExpansionOpen.Dimensions m upper,
            RowExpansionOpen.Expands (AugmentedGeneric.coefficientMixed p)
              (d.val+mixedCount m upper) (E d+mixedCount m upper*(m+1).choose 2) := by
  classical
  obtain ⟨E,hE,A,⟨a,ha⟩,hA⟩ := expansion_augmented (K := K) (L := L) m hm upper
  obtain ⟨B,⟨b,hb⟩,hB⟩ := EndpointF13AllRange.generic_endpoint_conditions (K := K) m (by omega) upper h2
  have hA0 : A ≠ 0 := by intro h; simp [h] at ha
  have hB0 : B ≠ 0 := by intro h; simp [h] at hb
  obtain ⟨p₀,hp₀⟩ := nonempty_principal_intersection
    (![A,B] : Fin 2 → MvPolynomial
      (AugmentedGeneric.ParameterIndex m (mixedCount m upper) (upperEndpoint m)) K)
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
theorem exists_fixed_open [Infinite K] (m : ℕ) (hm : 320 ≤ m) (upper : Bool)
    (h2 : (2 : K) ≠ 0) :
    ∃ g : Fin (mixedCount m upper) → Rows K m 1,
    ∃ r : Fin 4 → Forms K m 2,
    ∃ E : StrongExpansionOpen.Dimensions m upper → ℕ,
      StrongExpansionOpen.Thresholds m upper E ∧ LinearIndependent K g ∧
      (∀ d : StrongExpansionOpen.Dimensions m upper, RowExpansionOpen.Expands g
        (d.val+mixedCount m upper) (E d+mixedCount m upper*(m+1).choose 2)) ∧
      ∃ D : MvPolynomial (FixedBlockChildOpen.ChildIndex m (upperEndpoint m)) K,
        (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
          SimultaneousBlockConditions.BlockConditions
            (AugmentedGeneric.encode g (FixedBlockChildOpen.decode a) r) ∧
          GenericF13.Conditions g (FixedBlockChildOpen.decode a) ∧
          finrank K (CubicGeneric.CubicQuotient (FixedBlockChildOpen.decode a)) =
            (m+2).choose 3-m*upperEndpoint m := by
  classical
  obtain ⟨E,hE,D,⟨p₀,hp₀⟩,hD⟩ := common_open (K := K) (L := L) m hm upper h2
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

end Quartic.StrongExpansionCommonOpen
