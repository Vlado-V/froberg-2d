import Froberg.PreparedTargetSurjectivity
import Froberg.TargetLayerAssembly
import Froberg.LowRowsCommonOpen

/-! One actual prepared-family witness, simultaneously for every high
bidegree, from the common low-row and middle-row coefficients. -/
noncomputable section
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K] {h m d H r f u q : ℕ}
attribute [local instance] tensorGroup
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem exists_prepared_target_witness (hd : 3≤d)
    (frame : Fin H → Forms K h 2)
    (low : LowRowCoefficients K h m (d-1) (d-2) H f r)
    (hlow : LowRowsSurjective (by omega : d-2+d=(d-1)+(d-1)) frame low)
    (layer : MiddleTargetIndex d → HigherLayerIndex d)
    (hcover : ∀ b,(layer b).val<b.val.val ∧ b.val.val<2*(layer b).val)
    (G : BiformLayerFamily K h m (fun j : HigherLayerIndex d => j.val)
      (fun j => d-j.val) (fun j => higherGeneratorCount d h m j.val))
    (hG : ∀ b : MiddleTargetIndex d,Function.Surjective (biformTensorFamilyMap
      (x := b.val.val-(layer b).val) (y := d+(layer b).val-b.val.val) (G (layer b))))
    (S : Submodule K (Poly K h)) (hS : S≤Forms K h d)
    (u₀ : Fin u → S) (hu₀ : Submodule.span K (Set.range u₀)=⊤)
    (hcut : S*Forms K h 1=Forms K h (d+1)) (heven : ¬Odd d → S=Forms K h d)
    (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K)
    (hPdeg : ∀ i,(P i).IsHomogeneous d)
    (hPlow : ∀ i k,d≤k → coreComponent h m k (rename finSumFinEquiv (P i))=0) :
    ∃ p : Space m d q f u (activeEvenIndices d) (targetLayerCount d h m r) (targetLayerOutput frame),
      p.2.2=0 ∧ ∀ b,2≤b → b≤2*d → TargetLift
        ((Submodule.span K (Set.range (renamedGenerator
          (fun i => homogeneousInclusion S hS (u₀ i)) P p)))*Forms K (h+m) d) d b := by
  let T := targetLayerFamily hd frame low.2 G
  have hTmem := targetLayerFamily_mem hd frame low.2 G
  let p : Space m d q f u (activeEvenIndices d) (targetLayerCount d h m r) (targetLayerOutput frame) :=
    preparedTargetTensorParameters T hTmem low.1 0 0
  have hO (j) (_hj : j∈activeEvenIndices d) : targetLayerOutput frame j≤Forms K h j :=
    targetLayerOutput_homogeneous frame j
  have hJ (j) (hj : j∈activeEvenIndices d) : 0<j ∧ j≤d := by
    obtain ⟨h2,hlt,_⟩ := activeEvenIndices_bounds hd hj
    omega
  have hT (a : activeEvenIndices d) :
      preparedLayerTensor a (hO _ a.property) p.1=T a :=
    preparedLayerTensor_eq_of_values p.1 a (hO _ a.property) (T a) (fun _ => rfl)
  have hF : outerTensorFamily p=low.1 := by
    funext i
    exact LinearEquiv.symm_apply_apply sumBiformEquiv (low.1 i)
  have hE : quadraticTensorFamily (two_mem_activeEvenIndices hd)
      (hO 2 (two_mem_activeEvenIndices hd)) p=framedBiformFamily frame low.2 := by
    unfold quadraticTensorFamily
    rw [hT]
    funext i
    exact targetLayerFamily_quadratic hd frame low.2 G i
  refine ⟨p,rfl,?_⟩
  apply all_prepared_target_lifts hd hO hJ (two_mem_activeEvenIndices hd)
    S hS u₀ hu₀ hcut heven P hPdeg hPlow p
  · rw [hF,hE]
    exact hlow.1
  · rw [hE]
    exact hlow.2.1
  · rw [hE]
    exact hlow.2.2
  · intro b hb hbd hodd
    let bb : MiddleTargetIndex d := ⟨⟨b,by omega⟩,hb,hodd⟩
    let j := layer bb
    let a : activeEvenIndices d := ⟨j.val,(Finset.mem_filter.mp j.property).1⟩
    refine ⟨a,(hcover bb).1.le,by dsimp [a,j];omega,?_⟩
    rw [hT]
    exact targetLayerFamily_higher_surjective hd frame low.2 G j _ _ (hG bb)

end Froberg.PreparedTarget
