module

public import Froberg.OddAmbientBottom
public import Froberg.BiformComponentVanish
public import Froberg.SplitProjectionFactor

@[expose] public section

/-! Every vector in the bottom quotient has a literal weight-one
representative. Thus projections killing that weight factor through the
higher part of the corrected ambient coordinates. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable (hd : 1 ≤ d)
  (Q : Fin q → biformParitySpace K h m d 0)
  (F : Fin f → biformParitySpace K h m d 1)
  (hQ : ∀ i,(Q i).val.IsWeightedHomogeneous (blockWeight h m) 0)
  (hF : ∀ i,(F i).val.IsWeightedHomogeneous (blockWeight h m) 1)

theorem exists_odd_target_bottom_representative
    (x : OddTargetRowQuotient Q F (oddTargetBottomIndex hd)) :
    ∃ p : biformParitySpace K h m (2*d) 1,
      p.val.IsWeightedHomogeneous (blockWeight h m) 1 ∧
      (oddTargetBaseMap hd Q F hQ hF p).1=x := by
  obtain ⟨v,rfl⟩ := (coordinateRelation (oddBackgroundBlockRelations Q F)
    (oddTargetBottomIndex hd)).mkQ_surjective x
  let p := oddBiformEmbedding (by omega : 1 ≤ 2*d) (by decide) v
  refine ⟨p,?_,?_⟩
  · exact biformImage_output_weight (Forms K h 1) (Forms K m (2*d-1)) le_rfl
      (sumBiformMap_range.le ⟨v,rfl⟩)
  · rw [oddTargetBaseMap_bottom]
    congr 1
    rw [←biformTensorComponent_eq_oddCoordinates]
    exact biformTensorComponent_odd (by omega) (by omega) v

variable
  (G : Fin u → biformParitySpace K h m d 1)
  (D : HigherOddTargetRows hd Q F →ₗ[K] OddTargetRowQuotient Q F (oddTargetBottomIndex hd))
  (hD : D.comp (oddAmbientHigherRelationMap hd Q F hQ hF G)=
    oddAmbientBottomRelationMap hd Q F hQ hF G)

theorem exists_odd_ambient_bottom_representative
    (x : OddTargetRowQuotient Q F (oddTargetBottomIndex hd)) :
    ∃ p : biformParitySpace K h m (2*d) 1,
      p.val.IsWeightedHomogeneous (blockWeight h m) 1 ∧
      (oddAmbientCoordinates hd Q F hQ hF G D hD).symm (x,0)=
        (ambientOddRelations Q F G).mkQ p := by
  obtain ⟨p,hp,hpx⟩ := exists_odd_target_bottom_representative hd Q F hQ hF x
  refine ⟨p,hp,?_⟩
  apply (oddAmbientCoordinates hd Q F hQ hF G D hD).injective
  rw [LinearEquiv.apply_symm_apply,oddAmbientCoordinates_weighted_bottom hd Q F hQ hF G D hD p hp,hpx]

theorem odd_ambient_projection_kills_bottom {Z : Type} [AddCommGroup Z] [Module K Z]
    (proj : (biformParitySpace K h m (2*d) 1 ⧸ ambientOddRelations Q F G) →ₗ[K] Z)
    (hproj : ∀ p : biformParitySpace K h m (2*d) 1,
      p.val.IsWeightedHomogeneous (blockWeight h m) 1 →
        proj ((ambientOddRelations Q F G).mkQ p)=0)
    (x : OddTargetRowQuotient Q F (oddTargetBottomIndex hd)) :
    proj ((oddAmbientCoordinates hd Q F hQ hF G D hD).symm (x,0))=0 := by
  obtain ⟨p,hp,he⟩ := exists_odd_ambient_bottom_representative hd Q F hQ hF G D hD x
  rw [he]
  exact hproj p hp

end Froberg
