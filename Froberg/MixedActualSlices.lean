module

public import Froberg.MixedCovectorGrowth
public import Froberg.OddAffineSlices

@[expose] public section

/-! C.4 for the literal mixed U+P background: all higher contraction
estimates are obtained from the actual graded multiplication maps. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial TensorProduct Quartic Quartic.SplitTensor VectorMultiplicationCoordinates
open BilinearScalarFamily
attribute [local instance] tensorFormGroup
attribute [local irreducible] oddAmbientCoordinates oddAmbientHigherRelationMap oddAmbientBottomRelationMap
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K] {h m d q f u e b : ℕ}
variable (hd : Odd d) (hd3 : 3 ≤ d)
  (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1))
  (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
local notation "hdp" => Nat.le_trans (by decide : 1 ≤ 3) hd3
local notation "F" => bottomTensorFamily g
local notation "Q₀" => fun i => scalarEvenBiform (h := h) (Q i)
local notation "F₁" => fun i => oddBiformEmbedding hdp (by decide) (F i)
local notation "G₁" => fun i => mixedPureOddGenerator hd (U i) (P i)
local notation "hQ₀" => fun i => scalarEvenBiform_weighted (h := h) (Q i)
local notation "hF₁" => fun i => oddLinearBiform_weighted hdp (F i)
local notation "V" => biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F₁ G₁
local notation "W" => biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q₀ F₁ G₁
/-- Dimension of the literal mixed odd source. Naming it keeps finite-index
hypotheses from repeatedly elaborating the quotient presentation. -/
def mixedActualSourceDimension : ℕ := finrank K V

/-- Dimension of the literal mixed odd target. -/
def mixedActualTargetDimension : ℕ := finrank K W

attribute [local irreducible] mixedActualSourceDimension mixedActualTargetDimension
local notation "nV" => mixedActualSourceDimension hd hd3 g U P
local notation "nW" => mixedActualTargetDimension hd hd3 Q g U P
local notation "ν" => bottomCoordinateScalarAction hdp Q g
local notation "j" => nW-e*nV

theorem mixed_actual_affine_slices (hh : 0 < h) (hm : 0 < m)
    (hU : LinearIndependent K U)
    (hE : Disjoint ((rawTopFamily F).range.map (rawTopTarget hdp).toLinearMap)
      (leftRelations (Submodule.span K (Set.range U)) ⊔ rightRelations (Submodule.span K (Set.range Q))))
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (hR : Function.Surjective R)
    (hker : R.ker=(Submodule.span K (Set.range U)).map (topGrowthDegree hdp h).symm.toLinearMap)
    (s₀ : ℕ → ℕ) (hs₀ : HasClosedKernelSlices ν s₀) (M : ℕ)
    (htop : ∀ L : Submodule K (Fin b → K), M*finrank K L ≤ finrank K
      (BilinearImage.image (projectedTopScalarAction R (topGrowthParameters hdp Q F)) L))
    (hmid : ∀ (k : ℕ) (hk : 3 ≤ k) (hkd : k < d), k%2=1 →
      OddScalarLayerProperty M (by omega : 1 ≤ k) (by omega : k ≤ d)
        (F,fun i => scalarBiformEquiv (h := h) (Q i)))
    (E : Fin e → biformParitySpace K h m d 0)
    (P₀ : MvPolynomial (Fin (finrank K (Fin e → Forms K m d))) K)
    (hP₀ : ∃ a : Fin e → Forms K m d,eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0)
    (hinj : ∀ a,eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 →
      Function.Injective (oddEvenRelativeMap Q₀ F₁ G₁ (oddEvenAffineFamily E a)))
    (hupper : ∀ a,eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 →
      Function.Surjective (upperTargetMap (backgroundEnumeratedForms
        (Fin.append Q₀ (oddEvenAffineFamily E a)) F₁ G₁)))
    (slices : ℕ → ℕ) (hslices0 : j ≤ slices 0)
    (C L : ℕ) (loss : ℕ → ℕ)
    (hbase : ∀ k₀ : Fin (finrank K (OddBottomQuotient F)+1),0 < s₀ k₀.val →
      s₀ k₀.val+C*k₀.val ≤ finrank K (OddTargetRowQuotient Q₀ F₁ (oddTargetBottomIndex hdp)))
    (hslices : ∀ r : Fin (nV+1),0 < r.val → j ≤ slices r.val+loss r.val)
    (hC : L ≤ C) (hM : L ≤ M)
    (hloss : ∀ r : Fin (nV+1),0 < r.val → loss r.val ≤ L*r.val/2)
    (hsmall : 2*(higherRelationCost d h u m+nV+e)+1 ≤ L) :
    ∃ P₁ : MvPolynomial (Fin (finrank K (Fin e → Forms K m d))) K,
      (∃ a : Fin e → Forms K m d,eval ((Module.finBasis K _).equivFun a) P₁ ≠ 0) ∧
      ∀ a,eval ((Module.finBasis K _).equivFun a) P₁ ≠ 0 →
        eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 ∧
        HasClosedKernelSlices
          (targetPostcompose (oddBackgroundScalarProduct Q₀ F₁ G₁)
            (oddEvenAffineRelations Q₀ F₁ G₁ E a).mkQ) slices := by
  delta mixedActualSourceDimension mixedActualTargetDimension at hslices0 hslices hloss hsmall
  obtain ⟨B,hB⟩ := exists_odd_mixed_source_coordinates hd hd3 F U hU P
  obtain ⟨D,hD⟩ := exists_mixed_ambient_correction hdp hd (by omega) Q F U P hU hE
  let ec := oddAmbientCoordinates hdp Q₀ F₁ hQ₀ hF₁ G₁ D hD
  apply actual_odd_affine_slices Q₀ F₁ G₁ E hh hm hd ec
    (fun v hv => congrArg Prod.snd (oddAmbientCoordinates_weighted_bottom hdp Q₀ F₁ hQ₀ hF₁ G₁ D hD v hv))
    ν s₀ hs₀ M _ _ P₀ hP₀ hinj hupper slices hslices0 C L loss
    hbase hslices hC hM hloss hsmall
  · intro ell _
    exact mixed_full_bottom_kernel_finrank_le hd hd3 Q g U P B hB D hD ell
  · intro ell _
    exact mixed_full_higher_kernel_growth hd hd3 Q g U P B hB D hD R hR hker M htop hmid ell

end Froberg
