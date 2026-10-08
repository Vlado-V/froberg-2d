import Froberg.AmbientTopGrowth

/-! The C.10 separated tensor relation spaces are unchanged by the
explicit degree equalities 1+(d-1)=d. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg
open Module TensorProduct Quartic Quartic.SplitTensor
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m a b c e d q f n : ℕ}

theorem biformDegreeTransport_disjoint
    (ha : a=b) (hc : c=e)
    (P : Submodule K (Forms K h b)) (Q : Submodule K (Forms K m e))
    (E : Submodule K (Forms K h a ⊗[K] Forms K m c))
    (hE : Disjoint E
      (leftRelations (P.map (formDegreeEquiv ha).symm.toLinearMap) ⊔
        rightRelations (Q.map (formDegreeEquiv hc).symm.toLinearMap))) :
    Disjoint (E.map (biformDegreeTransport ha hc).toLinearMap)
      (leftRelations P ⊔ rightRelations Q) := by
  subst b
  subst e
  have ht : (biformDegreeTransport (K := K) (h := h) (m := m) (a := a) (c := c) rfl rfl).toLinearMap=LinearMap.id := by
    ext x y
    rfl
  have hx : (formDegreeEquiv (K := K) (n := h) (a := a) rfl).symm.toLinearMap=LinearMap.id := rfl
  have hy : (formDegreeEquiv (K := K) (n := m) (a := c) rfl).symm.toLinearMap=LinearMap.id := rfl
  rw [ht,Submodule.map_id]
  simpa only [hx,hy,Submodule.map_id] using hE

theorem top_degree_separation (hd : 1 ≤ d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin n → K))
    (Q : Fin q → Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Submodule K (Forms K h d))
    (hker : R.ker=U.map (topGrowthDegree hd h).symm.toLinearMap)
    (hi : Function.Injective (projectedTopMap R (topGrowthParameters hd Q F))) :
    Disjoint ((rawTopFamily F).range.map (rawTopTarget hd).toLinearMap)
      (leftRelations U ⊔ rightRelations (Submodule.span K (Set.range Q))) := by
  have hs := top_tensor_separation R F (fun i => (topGrowthDegree hd m).symm (Q i)) hi
  rw [hker] at hs
  have hQ : Submodule.span K (Set.range (fun i => (topGrowthDegree hd m).symm (Q i)))=
      (Submodule.span K (Set.range Q)).map (topGrowthDegree hd m).symm.toLinearMap := by
    rw [Submodule.map_span]
    congr 1
    exact Set.range_comp _ _
  rw [hQ] at hs
  exact biformDegreeTransport_disjoint (by omega) (by omega) U _ (rawTopFamily F).range hs

end Froberg
