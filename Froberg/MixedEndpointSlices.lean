import Froberg.MixedActualSlices
import Froberg.EndpointThinSlices
import Froberg.TopDegreeSeparation
import Froberg.PreparedLayeredBudget

/-! The odd mixed-background C.4 conclusion on the actual endpoint
quotient, with its true target dimension as the thin-slice index. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial TensorProduct Quartic Quartic.SplitTensor VectorMultiplicationCoordinates
open BilinearScalarFamily BilinearCovectorStrata
attribute [local instance] tensorFormGroup
attribute [local irreducible] mixedActualSourceDimension mixedActualTargetDimension
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K] {h m d q f u e b : ℕ}
variable (hd : Odd d) (hd3 : 3 ≤ d)
  (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1))
  (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
local notation "hdp" => Nat.le_trans (by decide : 1 ≤ 3) hd3
local notation "F" => bottomTensorFamily g
local notation "Q₀" => fun i => scalarEvenBiform (h := h) (Q i)
local notation "F₁" => fun i => oddBiformEmbedding hdp (by decide) (F i)
local notation "G₁" => fun i => mixedPureOddGenerator hd (U i) (P i)
local notation "V" => biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F₁ G₁
local notation "W" => biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q₀ F₁ G₁
local notation "T₀" => finrank K (OddTargetRowQuotient Q₀ F₁ (oddTargetBottomIndex hdp))
local notation "nV" => mixedActualSourceDimension hd hd3 g U P
local notation "nW" => mixedActualTargetDimension hd hd3 Q g U P
local notation "j" => nW-e*nV

theorem mixed_actual_thin_open (hh : 0 < h) (hm : 0 < m)
    (hU : LinearIndependent K U)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (hR : Function.Surjective R)
    (hker : R.ker=(Submodule.span K (Set.range U)).map (topGrowthDegree hdp h).symm.toLinearMap)
    (hi : Function.Injective (projectedTopMap R (topGrowthParameters hdp Q F)))
    (C S : ℝ) (hC : 0 ≤ C)
    (hs₀ : HasClosedKernelSlices (bottomCoordinateScalarAction hdp Q g) (thinSlices T₀ C))
    (M : ℕ)
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
    (L : ℕ) (hLC : L ≤ ⌊C⌋₊) (hLM : L ≤ M)
    (hloss : ∀ r : Fin (nV+1),0 < r.val → ⌈S*(r.val : ℝ)⌉₊ ≤ L*r.val/2)
    (hsmall : 2*(higherRelationCost d h u m+nV+e)+1 ≤ L) :
    ∃ P₁ : MvPolynomial (Fin (finrank K (Fin e → Forms K m d))) K,
      (∃ a : Fin e → Forms K m d,eval ((Module.finBasis K _).equivFun a) P₁ ≠ 0) ∧
      ∀ a,eval ((Module.finBasis K _).equivFun a) P₁ ≠ 0 →
        eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 ∧
        HasClosedKernelSlices (oddEndpointScalarAction (Fin.append Q₀ (oddEvenAffineFamily E a)) F₁ G₁)
          (thinSlices (finrank K (oddTargetSpace
            ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm)
            (backgroundEnumeratedForms (Fin.append Q₀ (oddEvenAffineFamily E a)) F₁ G₁))) S) := by
  have hE := top_degree_separation hdp R Q F (Submodule.span K (Set.range U)) hker hi
  have hz : j ≤ thinSlices j S 0 := by simp [thinSlices]
  have hbase : ∀ k₀ : Fin (finrank K (OddBottomQuotient F)+1),0 < thinSlices T₀ C k₀.val →
      thinSlices T₀ C k₀.val+⌊C⌋₊*k₀.val ≤ T₀ := by
    intro k hk
    exact thinSlices_positive_integer_base T₀ k C hC hk
  have hs : ∀ r : Fin (nV+1),0 < r.val →
      j ≤ thinSlices j S r.val+⌈S*(r.val : ℝ)⌉₊ := by
    intro r _
    unfold thinSlices
    omega
  obtain ⟨P₁,hP₁,hgood⟩ := mixed_actual_affine_slices hd hd3 Q g U P hh hm hU hE R hR hker
    (thinSlices T₀ C) hs₀ M htop hmid E P₀ hP₀ hinj hupper (thinSlices j S) hz
    ⌊C⌋₊ L (fun r => ⌈S*(r : ℝ)⌉₊) hbase hs hLC hLM hloss hsmall
  refine ⟨P₁,hP₁,?_⟩
  intro a ha
  obtain ⟨ha₀,hslices⟩ := hgood a ha
  delta mixedActualSourceDimension mixedActualTargetDimension at hslices
  exact ⟨ha₀,oddEndpointScalarAction_closed_thin_slices Q₀ F₁ G₁ (oddEvenAffineFamily E a)
    (hinj a ha₀) S hslices⟩

end Froberg
