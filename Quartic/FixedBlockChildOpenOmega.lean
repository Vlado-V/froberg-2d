module

public import Quartic.FixedBlockChildOpen
public import Quartic.ExpansionCommonOpenOmega
public import Quartic.MarkedEndpointFlag

@[expose] public section

/-! Fixing the mixed family while retaining a marked exact child flag. -/
noncomputable section
namespace Quartic.FixedBlockChildOpenOmega
open Module MvPolynomial RowMultiplicationCoordinates HomogeneousCoefficientCoordinates
open UniformEndpoint AugmentedGeneric FixedBlockChildOpen
variable {K : Type*} [Field K]
set_option maxHeartbeats 1000000

/-- Fix one mixed presentation on the common expansion locus. One child-only principal open
then preserves all block conditions and imposes the actual upper-child flag. -/
theorem exists_fixed_open [IsAlgClosed K] (ω : K) (m : ℕ) (hm : 41 ≤ m) (upper : Bool)
    (hω : ω ≠ 0) (hω1 : ω ≠ -1) (hchild : MarkedEndpoints K m) :
    ∃ g : Fin (mixedCount m upper) → Rows K m 1,
    ∃ r : Fin 4 → Forms K m 2,
    ∃ E : ConvolutionExpansionOpen.Dimensions m upper → ℕ,
      ConvolutionExpansionOpen.Thresholds m upper E ∧ LinearIndependent K g ∧
      (∀ d : ConvolutionExpansionOpen.Dimensions m upper,RowExpansionOpen.Expands g
        (d.val+mixedCount m upper) (E d+mixedCount m upper*(m+1).choose 2)) ∧
      ∃ D : MvPolynomial (ChildIndex m (upperEndpoint m)) K,
        (∃ a,eval a D ≠ 0) ∧ ∀ a,eval a D ≠ 0 →
          SimultaneousBlockConditionsOmega.BlockConditions ω (encode g (decode a) r) ∧
          GenericF13.Conditions g (decode a) ∧
          finrank K (CubicGeneric.CubicQuotient (decode a)) = (m+2).choose 3-m*upperEndpoint m ∧
          SharedChildFlag.Data (decode a) := by
  classical
  obtain ⟨E,hE,D,⟨p₀,hp₀⟩,hD⟩ := ExpansionCommonOpenOmega.common_open (K := K) (L := K)
    ω m hm upper hω hω1
  let g := coefficientMixed p₀
  let r := coefficientMotions p₀
  obtain ⟨hblock₀,hf₀,hc₀,hexp⟩ := hD p₀ hp₀
  let B := pullback g r D
  have hB : ∃ a,eval a B ≠ 0 := by
    refine ⟨encodeChild (coefficientChild p₀),?_⟩
    simpa only [B,eval_pullback,decode_encode,g,r,encode_recover] using hp₀
  obtain ⟨A,hA,hflag⟩ := MarkedEndpointFlag.principal_open (K := K) (by omega : 1 ≤ m)
    (upperEndpoint m) rfl decode (isPolynomialFamily_linear decode) decode_surjective hchild
  have hBn : B ≠ 0 := by obtain ⟨a,ha⟩ := hB; intro hz; simp [hz] at ha
  have hAn : A ≠ 0 := by obtain ⟨a,ha⟩ := hA; intro hz; simp [hz] at ha
  refine ⟨g,r,E,hE,hblock₀.1.1,hexp,A*B,
    PolynomialImageAvoidance.exists_eval_ne_zero (mul_ne_zero hAn hBn),?_⟩
  intro a ha
  rw [map_mul,mul_ne_zero_iff] at ha
  have hp : eval (encode g (decode a) r) D ≠ 0 := by
    simpa only [B,eval_pullback] using ha.2
  obtain ⟨hblock,hf,hc,_⟩ := hD _ hp
  refine ⟨hblock,?_,?_,hflag a ha.1⟩
  · simpa only [coefficientMixed_encode,coefficientChild_encode] using hf
  · have he := congrArg (fun h : Fin (upperEndpoint m) → Forms K m 2 =>
        finrank K (CubicGeneric.CubicQuotient h)) (coefficientChild_encode g (decode a) r)
    exact he.symm.trans hc

end Quartic.FixedBlockChildOpenOmega
