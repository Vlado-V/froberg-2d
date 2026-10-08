import Froberg.PreparedOddCommonOpen
import Froberg.PreparedAllEvenCounts
import Froberg.PureCutoffPolynomial

/-! The upper-target witness is transported to the same all-even parameter
space used by the relation and comparison theorems. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial PreparedParameters
variable {K : Type} [Field K] [CharZero K] {h m d H f r q u : ℕ}

theorem HasUpperWitness.all_even_variable_private_open (hd : 3 ≤ d)
    (frame : Fin H → Forms K h 2) (U : Fin u → Forms K h d)
    (P : OuterSpace K (Fin h) m d u)
    (hw : HasUpperWitness d f r q frame U (fun i => (P i).val)) :
    letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u
      (allEvenIndices d) (allEvenCount d h m r) (targetLayerOutput frame)) :=
      FullPreparedParameters.finite_fixedPureZeroScalarSpace
        (fun j _ => targetLayerOutput_homogeneous frame j)
    ∃ D : MvPolynomial (Fin (finrank K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u
      (allEvenIndices d) (allEvenCount d h m r) (targetLayerOutput frame)))) K,
      (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u
        (allEvenIndices d) (allEvenCount d h m r) (targetLayerOutput frame),
        eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u
        (allEvenIndices d) (allEvenCount d h m r) (targetLayerOutput frame),
        eval ((Module.finBasis K _).equivFun p) D≠0 →
          Function.Surjective (upperTargetMap (zeroScalarEndpointFamily (by omega : 0<d)
            (fun j _ => targetLayerOutput_homogeneous frame j)
            (fun j hj => (mem_allEvenIndices.mp hj).2.1) U p.1 p.2)) := by
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u
    (allEvenIndices d) (allEvenCount d h m r) (targetLayerOutput frame)) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace
      (fun j _ => targetLayerOutput_homogeneous frame j)
  obtain ⟨p,hzero,hlift⟩ := hw
  let p' := zeroLayers (activeEven_subset_allEven hd)
    (fun j hj => (allEvenCount_active h m r hj).symm)
    (fun j _ hj => allEvenCount_inactive h m r hj) p
  have hlift' := zeroLayers_target_lifts (activeEven_subset_allEven hd)
    (fun j hj => (allEvenCount_active h m r hj).symm)
    (fun j _ hj => allEvenCount_inactive h m r hj) p U (fun i => (P i).val) hlift
  have hp' : p'.2.2=0 := hzero
  let v := (p'.1,p'.2.1)
  have hv : zeroPrivateScalar v=p' := by
    refine Prod.ext rfl (Prod.ext rfl hp'.symm)
  have hup : Function.Surjective (upperTargetMap
      (enumerateForms (forms (by omega : 0<d)
        (fun j _ => targetLayerOutput_homogeneous frame j)
        (fun j hj => (mem_allEvenIndices.mp hj).2.1) U (fun i => (P i).val)
        (FullPreparedParameters.private_homogeneous (by omega) P) (zeroPrivateScalar v)))) := by
    apply upperTargetMap_surjective_of_lifts _ (by omega)
    rw [enumerate_forms_productSpace,hv]
    exact hlift'
  obtain ⟨D,hD,hgood⟩ := FullPreparedParameters.upper_target_open_fixed_pure_zero_scalar
    (by omega : 0<d) (fun j _ => targetLayerOutput_homogeneous frame j)
    (fun j hj => (mem_allEvenIndices.mp hj).2.1) U P v hup
  refine ⟨D,⟨(P,v),hD⟩,?_⟩
  intro z hz
  rw [zeroScalarEndpointFamily_eq_full]
  simpa only [LinearEquiv.symm_apply_apply] using hgood ((Module.finBasis K _).equivFun z) hz

end Froberg.PreparedTarget
