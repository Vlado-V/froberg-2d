module

public import Froberg.OddIntermediateSource
public import Froberg.OddSourceAllCoordinates

@[expose] public section

/-! The actual intermediate source projection is exactly the corresponding
coordinate of the full source decomposition, for arbitrary graph correction. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d f u : ℕ}

theorem oddMixedSourceBlockCoordinates_higher_mk (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (B : HigherOddCoordinates K h m d (Nat.le_trans (by decide : 1≤3) hd3) →ₗ[K] (Fin u → K))
    (hB : B.comp (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
      (fun i => mixedPureOddGenerator hd (U i) (P i)))=LinearMap.id)
    (v : biformParitySpace K h m d 1)
    (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex (Nat.le_trans (by decide : 1≤3) hd3)}) :
    (oddMixedSourceBlockCoordinates hd hd3 F U P B hB
      ((oddBackgroundCoefficientRelations
        (fun i => oddBiformEmbedding (t := 1) (Nat.le_trans (by decide : 1≤3) hd3) (by decide) (F i))
        (fun i => mixedPureOddGenerator hd (U i) (P i))).mkQ v)).2 r=
      (coordinateRelation (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
        (fun i => mixedPureOddGenerator hd (U i) (P i))).range r).mkQ
          (oddBiformCoordinatesEquiv v r.val) := rfl

theorem oddIntermediateSourceProjection_coordinates (hd : Odd d) (hd3 : 3≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (B : HigherOddCoordinates K h m d (Nat.le_trans (by decide : 1≤3) hd3) →ₗ[K] (Fin u → K))
    (hB : B.comp (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
      (fun i => mixedPureOddGenerator hd (U i) (P i)))=LinearMap.id)
    (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex (Nat.le_trans (by decide : 1≤3) hd3)})
    (hr : 2*r.val.val+1<d) (hb : 3≤2*r.val.val+1)
    (v : biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations
      (fun i => oddBiformEmbedding (t := 1) (Nat.le_trans (by decide : 1≤3) hd3) (by decide) (F i))
      (fun i => mixedPureOddGenerator hd (U i) (P i))) :
    oddIntermediateSourceProjection hd hb hr F U P v=
      oddHigherNonTopQuotientEquiv hd hd3 F U P r (by omega)
        ((oddMixedSourceBlockCoordinates hd hd3 F U P B hB v).2 r) := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change biformTensorComponent (by omega : 2*r.val.val+1 ≤ d) v=
      oddHigherNonTopQuotientEquiv hd hd3 F U P r (by omega)
        ((oddMixedSourceBlockCoordinates hd hd3 F U P B hB
          ((oddBackgroundCoefficientRelations _ _).mkQ v)).2 r)
    rw [oddMixedSourceBlockCoordinates_higher_mk]
    change biformTensorComponent (by omega : 2*r.val.val+1 ≤ d) v=oddBiformCoordinatesEquiv v r.val
    exact biformTensorComponent_eq_oddCoordinates v r.val

end Froberg
