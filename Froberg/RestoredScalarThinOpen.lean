module

public import Froberg.RestoredThinProperty
public import Froberg.EvenEndpointSlices
public import Froberg.OddSourceDimensionBudget
public import Froberg.EndpointThinProperty

@[expose] public section

/-! The finite even-degree endpoint estimate on the actual restored
scalar fiber preserves every condition on its supplied open. -/
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial VectorMultiplicationCoordinates BilinearScalarFamily BilinearCovectorStrata
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K] {h m d q f r : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}
variable (hd3 : 3 ≤ d) (hdeven : d%2=0)
  (hO : ∀ j ∈ J, O j ≤ Forms K h j) (hJ : ∀ j ∈ J, j ≤ d)
  (heven : ∀ j ∈ J, j%2=0) (idx : Fin r ≃ Label q J counts)
  (slot : Fin (finrank K (Forms K h d)) → Fin r)
  (hslot : ∀ k, 0 < degree (idx (slot k)))
  (rest : RestoredScalarRest m d q f J counts O)
local notation "hdp" => Nat.le_trans (by decide : 1 ≤ 3) hd3
local notation "Q" => Prod.fst (Prod.fst rest)
local notation "g" => fun i => PreparedTarget.outerVectorEquiv.symm (Prod.snd (Prod.snd rest) i)
local notation "F" => bottomTensorFamily g
local notation "Q₀" => fun i => scalarEvenBiform (h := h) (Q i)
local notation "F₁" => fun i => oddBiformEmbedding hdp (by decide) (F i)
local notation "T₀" => finrank K (OddTargetRowQuotient Q₀ F₁ (oddTargetBottomIndex hdp))

attribute [local irreducible] RestoredEndpointThin

include hslot in
theorem restored_scalar_thin_open (hh : 0 < h) (hm : 0 < m)
    (C S : ℝ) (hC : 0 ≤ C)
    (hbottom : HasClosedKernelSlices (bottomCoordinateScalarAction hdp Q g) (thinSlices T₀ C))
    (M : ℕ)
    (hmid : ∀ (k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d), k%2=1 →
      OddScalarLayerProperty M (by omega : 1 ≤ k) hkd
        (F,fun i => scalarBiformEquiv (h := h) (Q i)))
    (P₀ : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) m d J counts))) K)
    (hP₀ : ∃ a : PositiveScalars (K := K) m d J counts,
      eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0)
    (hgood : ∀ a, eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 →
      OddSplitExact
        (restoredBiformFamily hdeven hO hJ heven idx slot (restoredScalarFiberCoordinates.symm (a,rest)).1)
        (fun i => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (rest.2.2 i))) ∧
      Function.Surjective (upperTargetMap (restoredOuterEndpoint hdp hdeven hO hJ heven idx slot
        (restoredScalarFiberCoordinates.symm (a,rest)))))
    (L : ℕ) (hLC : L ≤ ⌊C⌋₊) (hLM : L ≤ M)
    (hloss : ∀ k : ℕ, ⌈S*(k : ℝ)⌉₊ ≤ L*k/2)
    (hsmall : 2*(oddCoefficientCount d h m+Fintype.card (ProductRows.LayerLabel J counts))+1 ≤ L) :
    ∃ P₁ : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) m d J counts))) K,
      (∃ a : PositiveScalars (K := K) m d J counts,
        eval ((Module.finBasis K _).equivFun a) P₁ ≠ 0) ∧
      ∀ a, eval ((Module.finBasis K _).equivFun a) P₁ ≠ 0 →
        eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 ∧
        RestoredEndpointThin hdp hdeven hO hJ heven idx slot S
          (restoredScalarFiberCoordinates.symm (a,rest)) := by
  let E := restoredPositiveBiform hdeven hO hJ heven idx slot
    (restoredScalarFiberCoordinates.symm (0,rest)).1
  have hf := linearOddForm_family_eq_embedding hdp g
  have hinj : ∀ a, eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 →
      Function.Injective (oddEvenRelativeMap Q₀ F₁ emptyOddFamily (oddEvenAffineFamily E a)) := by
    intro a ha
    have hi := restored_scalar_fiber_relative_injective hdp hdeven hO hJ heven idx slot hslot
      a rest (hgood a ha).1
    rw [hf] at hi
    exact hi
  have hupper : ∀ a, eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 →
      Function.Surjective (upperTargetMap (backgroundEnumeratedForms
        (Fin.append Q₀ (oddEvenAffineFamily E a)) F₁ emptyOddFamily)) := by
    intro a ha
    have hu := restored_scalar_fiber_upper hdp hdeven hO hJ heven idx slot hslot
      a rest (hgood a ha).2
    rw [hf] at hu
    exact hu
  have hdim : finrank K (EvenBackgroundSource hdp F) ≤ oddCoefficientCount d h m := by
    rw [(evenBackgroundSourceEquiv hdp F).finrank_eq]
    exact odd_biform_quotient_finrank_le_count hh hm _
  obtain ⟨P₁,hP₁,hthin⟩ := even_actual_thin_open hd3 Q g C S hC hbottom M hmid
    E P₀ hP₀ hinj hupper L hLC hLM (fun k _ => hloss k.val) (by omega)
  refine ⟨P₁,hP₁,?_⟩
  intro a ha
  obtain ⟨ha₀,hs⟩ := hthin a ha
  refine ⟨ha₀,?_⟩
  unfold RestoredEndpointThin
  change OddEndpointThin
    (Fin.append
      (restoredBaseBiform hdeven hO hJ heven idx slot
        (restoredScalarFiberCoordinates.symm (a,rest)).1)
      (restoredPositiveBiform hdeven hO hJ heven idx slot
        (restoredScalarFiberCoordinates.symm (a,rest)).1))
    (fun i => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (rest.2.2 i)))
    emptyOddFamily S
  rw [restoredBaseBiform_eq_scalar hdeven hO hJ heven idx slot hslot
      (restoredScalarFiberCoordinates.symm (a,rest)).1,
    restoredScalarFiber_positive hdeven hO hJ heven idx slot a rest,hf]
  exact hs

end Froberg.PreparedParameters
