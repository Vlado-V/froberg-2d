module

public import Froberg.AmbientTopGrowth
public import Froberg.OddSourceAllCoordinates

@[expose] public section

/-! The top source quotient is the actual quotient of pure forms by U,
and hence the projection target R. Degree transports match target growth. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d f u b : ℕ}

def topSourceMap (hdp : 1≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) : Forms K h d →ₗ[K] (Fin b → K) :=
  R.comp (topGrowthDegree hdp h).symm.toLinearMap

theorem topSourceMap_kernel (hdp : 1≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (U : Fin u → Forms K h d)
    (hker : R.ker=(Submodule.span K (Set.range U)).map (topGrowthDegree hdp h).symm.toLinearMap) :
    (topSourceMap hdp R).ker=Submodule.span K (Set.range U) := by
  ext x
  change R ((topGrowthDegree hdp h).symm x)=0 ↔ x∈Submodule.span K (Set.range U)
  rw [←LinearMap.mem_ker,hker]
  constructor
  · rintro ⟨y,hy,he⟩
    have hyx : y=x := (topGrowthDegree hdp h).symm.injective he
    exact hyx ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

def topSourceQuotientEquiv (hdp : 1≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (hR : Function.Surjective R)
    (U : Fin u → Forms K h d)
    (hker : R.ker=(Submodule.span K (Set.range U)).map (topGrowthDegree hdp h).symm.toLinearMap) :
    (Forms K h d ⧸ Submodule.span K (Set.range U)) ≃ₗ[K] (Fin b → K) :=
  (Submodule.quotEquivOfEq _ _ (topSourceMap_kernel hdp R U hker).symm).trans
    ((topSourceMap hdp R).quotKerEquivOfSurjective
      (hR.comp (topGrowthDegree hdp h).symm.surjective))

@[simp] theorem topSourceQuotientEquiv_mk (hdp : 1≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (hR : Function.Surjective R)
    (U : Fin u → Forms K h d)
    (hker : R.ker=(Submodule.span K (Set.range U)).map (topGrowthDegree hdp h).symm.toLinearMap)
    (v : Forms K h d) :
    topSourceQuotientEquiv hdp R hR U hker ((Submodule.span K (Set.range U)).mkQ v)=
      R ((topGrowthDegree hdp h).symm v) := rfl

def oddHigherTopProjectionEquiv (hd : Odd d) (hd3 : 3≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (hR : Function.Surjective R)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (hker : R.ker=(Submodule.span K (Set.range U)).map
      (topGrowthDegree (Nat.le_trans (by decide : 1≤3) hd3) h).symm.toLinearMap)
    (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex (Nat.le_trans (by decide : 1≤3) hd3)})
    (hr : 2*r.val.val+1=d) :
    (OddHigherBlock K h m d (Nat.le_trans (by decide : 1≤3) hd3) r ⧸
      coordinateRelation (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
        (fun i => mixedPureOddGenerator hd (U i) (P i))).range r) ≃ₗ[K] (Fin b → K) :=
  (oddHigherTopQuotientEquiv hd hd3 F U P r hr).trans
    (topSourceQuotientEquiv (Nat.le_trans (by decide : 1≤3) hd3) R hR U hker)

@[simp] theorem oddHigherTopProjectionEquiv_mk (hd : Odd d) (hd3 : 3≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (hR : Function.Surjective R)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (hker : R.ker=(Submodule.span K (Set.range U)).map
      (topGrowthDegree (Nat.le_trans (by decide : 1≤3) hd3) h).symm.toLinearMap)
    (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex (Nat.le_trans (by decide : 1≤3) hd3)})
    (hr : 2*r.val.val+1=d) (v : OddHigherBlock K h m d (Nat.le_trans (by decide : 1≤3) hd3) r) :
    oddHigherTopProjectionEquiv hd hd3 R hR F U P hker r hr
      ((coordinateRelation (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
        (fun i => mixedPureOddGenerator hd (U i) (P i))).range r).mkQ v)=
      R ((topGrowthDegree (Nat.le_trans (by decide : 1≤3) hd3) h).symm
        ((oddHigherPureEquiv (m := m) (Nat.le_trans (by decide : 1≤3) hd3) r hr).symm v)) := rfl

end Froberg
