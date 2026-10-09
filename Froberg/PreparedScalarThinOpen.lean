module

public import Froberg.PreparedThinProperty
public import Froberg.EndpointThinProperty
public import Froberg.MixedEndpointSlices
public import Froberg.CountedBaseC4Growth
public import Froberg.OddSourceDimensionBudget

@[expose] public section

/-! Apply the actual odd quotient estimate on a frozen prepared scalar
fiber. The input open retains all geometric certificates already imposed. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency true
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial PreparedParameters BilinearScalarFamily BilinearCovectorStrata
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K] {h m d q f u b : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}
variable (hd3 : 3 ≤ d) (hdodd : d%2=1)
  (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
  (U : Fin u → Forms K h d) (rest : FullScalarFiberRest m d q f u J counts O)
local notation "hdp" => Nat.le_trans (by decide : 1 ≤ 3) hd3
local notation "Q" => Prod.fst (Prod.fst (Prod.snd rest))
local notation "g" => fun i => outerVectorEquiv.symm ((Prod.snd (Prod.snd rest)) i)
local notation "F" => bottomTensorFamily g
local notation "Q₀" => fun i => scalarEvenBiform (h := h) (Q i)
local notation "F₁" => fun i => oddBiformEmbedding hdp (by decide) (F i)
local notation "T₀" => finrank K (OddTargetRowQuotient Q₀ F₁ (oddTargetBottomIndex hdp))

theorem prepared_scalar_thin_open (hh : 0 < h) (hm : 0 < m)
    (hU : LinearIndependent K U)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (hR : Function.Surjective R)
    (hker : R.ker=(Submodule.span K (Set.range U)).map (topGrowthDegree hdp h).symm.toLinearMap)
    (C S : ℝ) (hC : 0 ≤ C)
    (hbottom : HasClosedKernelSlices (bottomCoordinateScalarAction hdp Q g) (thinSlices T₀ C))
    (M : ℕ) (hgrowth : BaseC4GrowthProperty hdp R M (F,Q))
    (P₀ : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) m d J counts))) K)
    (hP₀ : ∃ a : PositiveScalars (K := K) m d J counts,
      eval ((Module.finBasis K _).equivFun a) P₀≠0)
    (hgood : ∀ a,eval ((Module.finBasis K _).equivFun a) P₀≠0 →
      OddCyclesExact U rest.1 (scalarFiberCoordinates.symm (a,rest.2.1),rest.2.2) ∧
      Function.Surjective (upperTargetMap (zeroScalarEndpointFamily (by omega : 0 < d) hO hJ U rest.1
        (scalarFiberCoordinates.symm (a,rest.2.1),rest.2.2))))
    (L : ℕ) (hLC : L ≤ ⌊C⌋₊) (hLM : L ≤ M)
    (hloss : ∀ r : ℕ,⌈S*(r : ℝ)⌉₊ ≤ L*r/2)
    (hsmall : 2*(higherRelationCost d h u m+oddCoefficientCount d h m+
      Fintype.card (ProductRows.LayerLabel J counts))+1 ≤ L) :
    ∃ P₁ : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) m d J counts))) K,
      (∃ a : PositiveScalars (K := K) m d J counts,
        eval ((Module.finBasis K _).equivFun a) P₁≠0) ∧
      ∀ a,eval ((Module.finBasis K _).equivFun a) P₁≠0 →
        eval ((Module.finBasis K _).equivFun a) P₀≠0 ∧
        PreparedEndpointThin (by omega : 0 < d) hdodd hO hJ heven U S
          (fullScalarFiberCoordinates.symm (a,rest)) := by
  let P := fun i => sumBiformEquiv.symm (rest.1 i)
  let E := preparedHighBiform hO hJ heven (scalarFiberCoordinates.symm (0,rest.2.1))
  have hf := preparedOddBiform_outer_family (by omega : 0 < d) hdodd U rest.1 rest.2.2
  have hp := preparedOddBiform_private_family (by omega : 0 < d) hdodd U rest.1 rest.2.2
  have hinj : ∀ a,eval ((Module.finBasis K _).equivFun a) P₀≠0 →
      Function.Injective (oddEvenRelativeMap Q₀ F₁
        (fun i => mixedPureOddGenerator (Nat.odd_iff.mpr hdodd) (U i) (P i))
        (oddEvenAffineFamily E a)) := by
    intro a ha
    have hi := prepared_scalar_fiber_relative_injective (by omega : 0 < d) hdodd hO hJ heven
      U rest a (hgood a ha).1
    rw [hf,hp] at hi
    exact hi
  have hupper : ∀ a,eval ((Module.finBasis K _).equivFun a) P₀≠0 →
      Function.Surjective (upperTargetMap (backgroundEnumeratedForms
        (Fin.append Q₀ (oddEvenAffineFamily E a)) F₁
        (fun i => mixedPureOddGenerator (Nat.odd_iff.mpr hdodd) (U i) (P i)))) := by
    intro a ha
    have hu := prepared_scalar_fiber_upper (by omega : 0 < d) hdodd hO hJ heven
      U rest a (hgood a ha).2
    rw [hf,hp] at hu
    exact hu
  have hdim := odd_biform_quotient_finrank_le_count (d := d) hh hm
    (oddBackgroundCoefficientRelations F₁
      (fun i => mixedPureOddGenerator (Nat.odd_iff.mpr hdodd) (U i) (P i)))
  obtain ⟨P₁,hP₁,hthin⟩ := mixed_actual_thin_open (Nat.odd_iff.mpr hdodd) hd3 Q g U P
    hh hm hU R hR hker hgrowth.1 C S hC hbottom M hgrowth.2.1
    (fun k hk hkd _ => hgrowth.2.2 k hk (Nat.le_of_lt hkd)) E P₀ hP₀ hinj hupper
    L hLC hLM (fun r _ => hloss r.val) (by dsimp only [mixedActualSourceDimension]; omega)
  refine ⟨P₁,hP₁,?_⟩
  intro a ha
  obtain ⟨ha₀,hs⟩ := hthin a ha
  refine ⟨ha₀,?_⟩
  change PreparedEndpointThin (by omega : 0 < d) hdodd hO hJ heven U S
    (rest.1,(scalarFiberCoordinates.symm (a,rest.2.1),rest.2.2))
  change OddEndpointThin
    (Fin.append (preparedBaseBiform hO hJ heven (scalarFiberCoordinates.symm (a,rest.2.1)))
      (preparedPositiveBiform hO hJ heven (scalarFiberCoordinates.symm (a,rest.2.1))))
    (fun i => preparedOddBiform (by omega : 0 < d) hdodd U rest.1 rest.2.2 (Sum.inl i))
    (fun i => preparedOddBiform (by omega : 0 < d) hdodd U rest.1 rest.2.2 (Sum.inr i)) S
  rw [scalarFiber_base hO hJ heven a rest.2.1,
    scalarFiber_positive hO hJ heven a rest.2.1,hf,hp]
  exact hs

end Froberg.PreparedTarget
