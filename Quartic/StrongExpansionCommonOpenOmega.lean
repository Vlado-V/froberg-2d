module

public import Quartic.StrongExpansionCommonOpen
public import Quartic.EndpointF13AllRangeOmega

@[expose] public section

/-! The strong common expansion open with the modified pure quadratic pencil.
The parameter avoids only zero and minus one, so the construction applies
also in characteristic two. The child and all mixed columns remain literal. -/
noncomputable section
namespace Quartic.StrongExpansionCommonOpenOmega
open Module MvPolynomial RowMultiplicationCoordinates RowExpansionOpen
open UniformEndpoint ProfileCertificate
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]

include L in
theorem common_open [Infinite K] (ω : K) (m : ℕ) (hm : 320 ≤ m) (upper : Bool) (hω : ω ≠ 0) (hω1 : ω ≠ -1) :
    ∃ E : StrongExpansionOpen.Dimensions m upper → ℕ,
      StrongExpansionOpen.Thresholds m upper E ∧
      ∃ D : MvPolynomial (AugmentedGeneric.ParameterIndex m (mixedCount m upper) (upperEndpoint m)) K,
        (∃ p, eval p D ≠ 0) ∧ ∀ p, eval p D ≠ 0 →
          SimultaneousBlockConditionsOmega.BlockConditions ω p ∧
          GenericF13.Conditions (AugmentedGeneric.coefficientMixed p) (AugmentedGeneric.coefficientChild p) ∧
          finrank K (CubicGeneric.CubicQuotient (AugmentedGeneric.coefficientChild p)) =
            (m+2).choose 3-m*upperEndpoint m ∧
          ∀ d : StrongExpansionOpen.Dimensions m upper,
            RowExpansionOpen.Expands (AugmentedGeneric.coefficientMixed p)
              (d.val+mixedCount m upper) (E d+mixedCount m upper*(m+1).choose 2) := by
  classical
  obtain ⟨E,hE,A,⟨a,ha⟩,hA⟩ := StrongExpansionCommonOpen.expansion_augmented (K := K) (L := L) m hm upper
  obtain ⟨B,⟨b,hb⟩,hB⟩ := EndpointF13AllRangeOmega.generic_endpoint_conditions (K := K) ω m (by omega) upper hω hω1
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
theorem exists_fixed_open [Infinite K] (ω : K) (m : ℕ) (hm : 320 ≤ m) (upper : Bool)
    (hω : ω ≠ 0) (hω1 : ω ≠ -1) :
    ∃ g : Fin (mixedCount m upper) → Rows K m 1,
    ∃ r : Fin 4 → Forms K m 2,
    ∃ E : StrongExpansionOpen.Dimensions m upper → ℕ,
      StrongExpansionOpen.Thresholds m upper E ∧ LinearIndependent K g ∧
      (∀ d : StrongExpansionOpen.Dimensions m upper, RowExpansionOpen.Expands g
        (d.val+mixedCount m upper) (E d+mixedCount m upper*(m+1).choose 2)) ∧
      ∃ D : MvPolynomial (FixedBlockChildOpen.ChildIndex m (upperEndpoint m)) K,
        (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
          SimultaneousBlockConditionsOmega.BlockConditions ω
            (AugmentedGeneric.encode g (FixedBlockChildOpen.decode a) r) ∧
          GenericF13.Conditions g (FixedBlockChildOpen.decode a) ∧
          finrank K (CubicGeneric.CubicQuotient (FixedBlockChildOpen.decode a)) =
            (m+2).choose 3-m*upperEndpoint m := by
  classical
  obtain ⟨E,hE,D,⟨p₀,hp₀⟩,hD⟩ := common_open (K := K) (L := L) ω m hm upper hω hω1
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
theorem exists_fixed_open_with [Infinite K] (ω : K) (m : ℕ) (hm : 320 ≤ m) (upper : Bool)
    (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (A : MvPolynomial (AugmentedGeneric.ParameterIndex m (mixedCount m upper) (upperEndpoint m)) K)
    (hA : ∃ p, eval p A ≠ 0) :
    ∃ g : Fin (mixedCount m upper) → Rows K m 1,
    ∃ r : Fin 4 → Forms K m 2,
    ∃ E : StrongExpansionOpen.Dimensions m upper → ℕ,
      StrongExpansionOpen.Thresholds m upper E ∧ LinearIndependent K g ∧
      (∀ d : StrongExpansionOpen.Dimensions m upper, RowExpansionOpen.Expands g
        (d.val+mixedCount m upper) (E d+mixedCount m upper*(m+1).choose 2)) ∧
      ∃ D : MvPolynomial (FixedBlockChildOpen.ChildIndex m (upperEndpoint m)) K,
        (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
          SimultaneousBlockConditionsOmega.BlockConditions ω
            (AugmentedGeneric.encode g (FixedBlockChildOpen.decode a) r) ∧
          GenericF13.Conditions g (FixedBlockChildOpen.decode a) ∧
          finrank K (CubicGeneric.CubicQuotient (FixedBlockChildOpen.decode a)) =
            (m+2).choose 3-m*upperEndpoint m ∧
          eval (AugmentedGeneric.encode g (FixedBlockChildOpen.decode a) r) A ≠ 0 := by
  classical
  obtain ⟨E,hE,D,⟨p,hp⟩,hD⟩ := common_open (K := K) (L := L) ω m hm upper hω hω1
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

end Quartic.StrongExpansionCommonOpenOmega
