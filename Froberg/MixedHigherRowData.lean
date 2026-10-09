module

public import Froberg.OddIntermediateCoordinates
public import Froberg.OddActualRowGrowth
public import Froberg.TopSourceCoordinates
public import Froberg.AmbientTopVanish
public import Froberg.PiHigherProjectedGrowth
public import Froberg.OddAmbientBottomRepresentatives

@[expose] public section

/-! Concrete top and middle target projections for every higher block of
the actual mixed odd source. Both choices are placed in a common product
so their target spaces need no dependent case split. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial TensorProduct Quartic
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f u b : ℕ}

abbrev MixedHigherIndex (d : ℕ) (hd3 : 3≤d) :=
  {r : Fin ((d+1)/2) // r≠oddBottomIndex (Nat.le_trans (by decide : 1≤3) hd3)}

abbrev MixedHigherSource (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (r : MixedHigherIndex d hd3) :=
  OddHigherBlock K h m d (Nat.le_trans (by decide : 1≤3) hd3) r ⧸
    coordinateRelation (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
      (fun i => mixedPureOddGenerator hd (U i) (P i))).range r

abbrev MixedAmbientSource (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1)) :=
  biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations
    (fun i => oddBiformEmbedding (Nat.le_trans (by decide : 1≤3) hd3) (by decide) (F i))
    (fun i => mixedPureOddGenerator hd (U i) (P i))

abbrev MixedAmbientTarget (hd : Odd d) (hd3 : 3≤d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1)) :=
  biformParitySpace K h m (2*d) 1 ⧸ ambientOddRelations
    (fun i => scalarEvenBiform (h := h) (Q i))
    (fun i => oddBiformEmbedding (Nat.le_trans (by decide : 1≤3) hd3) (by decide) (F i))
    (fun i => mixedPureOddGenerator hd (U i) (P i))

abbrev MixedTopTarget (hd3 : 3≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :=
  ((Fin b → K) ⊗[K] Forms K m (1+(d-1))) ⧸
    (projectedTensorFamily (K := K) (A := Fin f → Forms K h (d-1) ⊗[K] Forms K m 1)
      R (rawTopFamily F) (topGrowthParameters (Nat.le_trans (by decide : 1≤3) hd3) Q F).2).range

abbrev MixedMiddleTarget (hd3 : 3≤d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (r : MixedHigherIndex d hd3) :=
  OddRowTensor K h m (2*r.val.val+1) (2*d-(2*r.val.val+1)) ⧸
    tensorOddRowRelations (b := 2*r.val.val+1) (by omega) (by have := r.val.isLt; omega)
      (fun i => scalarBiformEquiv (h := h) (Q i)) F

abbrev MixedHigherTarget (hd3 : 3≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (r : MixedHigherIndex d hd3) :=
  MixedTopTarget hd3 R Q F × MixedMiddleTarget hd3 Q F r

 theorem mixedHigherIndex_ge_three (hd3 : 3≤d) (r : MixedHigherIndex d hd3) :
    3≤2*r.val.val+1 := by
  have hr : r.val.val≠0 := by
    intro hz
    apply r.property
    exact Fin.ext hz
  omega

 theorem mixedProjectionKillsU (hd3 : 3≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (U : Fin u → Forms K h d)
    (hker : R.ker=(Submodule.span K (Set.range U)).map
      (topGrowthDegree (Nat.le_trans (by decide : 1≤3) hd3) h).symm.toLinearMap)
    (i : Fin u) :
    R ((topGrowthDegree (Nat.le_trans (by decide : 1≤3) hd3) h).symm (U i))=0 := by
  apply (show (topGrowthDegree (Nat.le_trans (by decide : 1≤3) hd3) h).symm (U i)∈R.ker from ?_)
  rw [hker]
  exact ⟨U i,Submodule.subset_span ⟨i,rfl⟩,rfl⟩

def mixedAmbientScalar (hd : Odd d) (hd3 : 3≤d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    Forms K m d →ₗ[K] MixedAmbientSource hd hd3 F U P →ₗ[K] MixedAmbientTarget hd hd3 Q F U P :=
  (oddAmbientScalarProduct
    (fun i => scalarEvenBiform (h := h) (Q i))
    (fun i => oddBiformEmbedding (Nat.le_trans (by decide : 1≤3) hd3) (by decide) (F i))
    (fun i => mixedPureOddGenerator hd (U i) (P i))).comp scalarBiformEquiv.toLinearMap

@[simp] theorem mixedAmbientScalar_mk (hd : Odd d) (hd3 : 3≤d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (p : Forms K m d) (v : biformParitySpace K h m d 1) :
    mixedAmbientScalar hd hd3 Q F U P p ((oddBackgroundCoefficientRelations _ _).mkQ v)=
      (ambientOddRelations _ _ _).mkQ (evenScalarOddProduct (scalarEvenBiform (h := h) p) v) := rfl

def mixedHigherProjection (hd : Odd d) (hd3 : 3≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (hker : R.ker=(Submodule.span K (Set.range U)).map
      (topGrowthDegree (Nat.le_trans (by decide : 1≤3) hd3) h).symm.toLinearMap)
    (r : MixedHigherIndex d hd3) :
    MixedAmbientTarget hd hd3 Q F U P →ₗ[K] MixedHigherTarget hd3 R Q F r :=
  if ht : 2*r.val.val+1=d then
    (ambientTopGrowthProjection (Nat.le_trans (by decide : 1≤3) hd3) hd (by omega) R Q F U P
      (mixedProjectionKillsU hd3 R U hker)).prod 0
  else
    (0 : MixedAmbientTarget hd hd3 Q F U P →ₗ[K] MixedTopTarget hd3 R Q F).prod
      (oddAmbientRowProjection hd (mixedHigherIndex_ge_three hd3 r)
        (by have := r.val.isLt; omega) (by omega) (fun i => scalarBiformEquiv (h := h) (Q i)) F U P)

def mixedHigherAction (hd : Odd d) (hd3 : 3≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (hR : Function.Surjective R)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (hker : R.ker=(Submodule.span K (Set.range U)).map
      (topGrowthDegree (Nat.le_trans (by decide : 1≤3) hd3) h).symm.toLinearMap)
    (r : MixedHigherIndex d hd3) :
    Forms K m d →ₗ[K] MixedHigherSource hd hd3 F U P r →ₗ[K] MixedHigherTarget hd3 R Q F r :=
  if ht : 2*r.val.val+1=d then
    ((topGrowthScalarAction (Nat.le_trans (by decide : 1≤3) hd3) R Q F).compl₂
      (oddHigherTopProjectionEquiv hd hd3 R hR F U P hker r ht).toLinearMap).compr₂ₛₗ
        (LinearMap.inl K (MixedTopTarget hd3 R Q F) (MixedMiddleTarget hd3 Q F r))
  else
    ((oddActualRowScalarAction (b := 2*r.val.val+1) (by omega) (by have := r.val.isLt; omega) Q F).compl₂
      (oddHigherNonTopQuotientEquiv hd hd3 F U P r ht).toLinearMap).compr₂ₛₗ
        (LinearMap.inr K (MixedTopTarget hd3 R Q F) (MixedMiddleTarget hd3 Q F r))

end Froberg
