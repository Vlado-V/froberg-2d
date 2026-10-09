module

public import Froberg.EvenActualSlices
public import Froberg.EndpointThinSlices
public import Froberg.PreparedLayeredBudget

@[expose] public section

/-! The even-background C.4 conclusion on the actual enlarged endpoint. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial TensorProduct Quartic VectorMultiplicationCoordinates
open BilinearScalarFamily BilinearCovectorStrata
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K] {h m d q f e : ℕ}
variable (hd3 : 3 ≤ d) (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1))
local notation "hdp" => Nat.le_trans (by decide : 1 ≤ 3) hd3
local notation "F" => bottomTensorFamily g
local notation "Q₀" => fun i => scalarEvenBiform (h := h) (Q i)
local notation "F₁" => fun i => oddBiformEmbedding hdp (by decide) (F i)
local notation "V" => EvenBackgroundSource hdp F
local notation "W" => EvenBackgroundTarget hdp Q F
local notation "T₀" => finrank K (OddTargetRowQuotient Q₀ F₁ (oddTargetBottomIndex hdp))
local notation "j" => finrank K W-e*finrank K V

theorem evenEndpointScalarAction_target_finrank
    (E : Fin e → biformParitySpace K h m d 0)
    (hi : Function.Injective (oddEvenRelativeMap Q₀ F₁ emptyOddFamily E)) :
    finrank K (oddTargetSpace ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm)
      (backgroundEnumeratedForms (Fin.append Q₀ E) F₁ emptyOddFamily))=j := by
  rw [oddEndpointScalarAction_target_finrank Q₀ F₁ emptyOddFamily E hi]
  rw [←(evenBackgroundTargetEquiv hdp Q F).finrank_eq,
    ←(evenBackgroundSourceEquiv hdp F).finrank_eq]

theorem even_actual_thin_open
    (C S : ℝ) (hC : 0 ≤ C)
    (hs₀ : HasClosedKernelSlices (bottomCoordinateScalarAction hdp Q g) (thinSlices T₀ C))
    (M : ℕ)
    (hmid : ∀ (k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d), k%2=1 →
      OddScalarLayerProperty M (by omega : 1 ≤ k) hkd
        (F,fun i => scalarBiformEquiv (h := h) (Q i)))
    (E : Fin e → biformParitySpace K h m d 0)
    (P₀ : MvPolynomial (Fin (finrank K (Fin e → Forms K m d))) K)
    (hP₀ : ∃ a : Fin e → Forms K m d,eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0)
    (hinj : ∀ a,eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 →
      Function.Injective (oddEvenRelativeMap Q₀ F₁ emptyOddFamily (oddEvenAffineFamily E a)))
    (hupper : ∀ a,eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 →
      Function.Surjective (upperTargetMap (backgroundEnumeratedForms
        (Fin.append Q₀ (oddEvenAffineFamily E a)) F₁ emptyOddFamily)))
    (L : ℕ) (hLC : L ≤ ⌊C⌋₊) (hLM : L ≤ M)
    (hloss : ∀ r : Fin (finrank K V+1),0 < r.val → ⌈S*(r.val : ℝ)⌉₊ ≤ L*r.val/2)
    (hsmall : 2*(finrank K V+e)+1 ≤ L) :
    ∃ P₁ : MvPolynomial (Fin (finrank K (Fin e → Forms K m d))) K,
      (∃ a : Fin e → Forms K m d,eval ((Module.finBasis K _).equivFun a) P₁ ≠ 0) ∧
      ∀ a,eval ((Module.finBasis K _).equivFun a) P₁ ≠ 0 →
        eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 ∧
        HasClosedKernelSlices (oddEndpointScalarAction (Fin.append Q₀ (oddEvenAffineFamily E a)) F₁ emptyOddFamily)
          (thinSlices (finrank K (oddTargetSpace
            ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm)
            (backgroundEnumeratedForms (Fin.append Q₀ (oddEvenAffineFamily E a)) F₁ emptyOddFamily))) S) := by
  have hz : j ≤ thinSlices j S 0 := by simp [thinSlices]
  have hbase : ∀ k₀ : Fin (finrank K (OddBottomQuotient F)+1),0 < thinSlices T₀ C k₀.val →
      thinSlices T₀ C k₀.val+⌊C⌋₊*k₀.val ≤ T₀ := by
    intro k hk
    exact thinSlices_positive_integer_base T₀ k C hC hk
  have hs : ∀ r : Fin (finrank K V+1),0 < r.val →
      j ≤ thinSlices j S r.val+⌈S*(r.val : ℝ)⌉₊ := by
    intro r _
    unfold thinSlices
    omega
  obtain ⟨P₁,hP₁,hgood⟩ := even_actual_affine_slices hd3 Q g
    (thinSlices T₀ C) hs₀ M hmid E P₀ hP₀ hinj hupper (thinSlices j S) hz
    ⌊C⌋₊ L (fun r => ⌈S*(r : ℝ)⌉₊) hbase hs hLC hLM hloss hsmall
  refine ⟨P₁,hP₁,?_⟩
  intro a ha
  obtain ⟨ha₀,hslices⟩ := hgood a ha
  refine ⟨ha₀,?_⟩
  rw [evenEndpointScalarAction_target_finrank hd3 Q g (oddEvenAffineFamily E a) (hinj a ha₀)]
  exact evenRelative_closed_slices hdp Q F (oddEvenAffineFamily E a) _ hslices

end Froberg
