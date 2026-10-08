import Froberg.PreparedTargetEventual
import Froberg.PreparedTargetEnumeration

/-! Rank-open certificates in the actual full prepared parameter space,
and in its odd-parity restriction with zero private scalar shifts. -/
noncomputable section
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [CharZero K] {h m d H f r q u : ℕ}
attribute [local instance] tensorGroup

local instance targetSpaceFinite (frame : Fin H → Forms K h 2) :
    Module.Finite K (Space m d q f u (activeEvenIndices d)
      (targetLayerCount d h m r) (targetLayerOutput frame)) :=
  finite_space (fun j _ => targetLayerOutput_homogeneous frame j)

local instance targetRestrictedSpaceFinite (frame : Fin H → Forms K h 2) :
    Module.Finite K (PreparedParameters.Space m d q (activeEvenIndices d)
      (targetLayerCount d h m r) (targetLayerOutput frame) × OuterSpace K (Fin h) m d f) := by
  letI := PreparedParameters.finite_space (n := m) (d := d) (q := q)
    (J := activeEvenIndices d) (counts := targetLayerCount d h m r)
    (fun j _ => targetLayerOutput_homogeneous frame j)
  letI : Module.Finite K (biformImage (Forms K h 1) (Forms K m (d-1))) :=
    Module.Finite.of_surjective sumBiformEquiv.toLinearMap sumBiformEquiv.surjective
  unfold OuterSpace
  infer_instance

/-- A literal successful point, suitable for a larger polynomial parameter
space in which the private terms and the pure tuple also vary. -/
theorem HasUpperWitness.exists_upperTarget_surjective (hd : 3≤d)
    (frame : Fin H → Forms K h 2) (U : Fin u → Forms K h d)
    (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K) (hP : ∀ i,(P i).IsHomogeneous d)
    (hw : HasUpperWitness d f r q frame U P) :
    ∃ p : Space m d q f u (activeEvenIndices d)
        (targetLayerCount d h m r) (targetLayerOutput frame),
      p.2.2=0 ∧ Function.Surjective (upperTargetMap
        (enumerateForms (forms (by omega : 0<d)
          (fun j _ => targetLayerOutput_homogeneous frame j)
          (fun j hj => (activeEvenIndices_bounds hd hj).2.1.le) U P hP p))) := by
  obtain ⟨p,hzero,hlift⟩ := hw
  refine ⟨p,hzero,upperTargetMap_surjective_of_lifts _ (by omega) ?_⟩
  simpa only [enumerate_forms_productSpace] using hlift

theorem HasUpperWitness.exists_full_rank_open (hd : 3≤d)
    (frame : Fin H → Forms K h 2) (U : Fin u → Forms K h d)
    (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K) (hP : ∀ i,(P i).IsHomogeneous d)
    (hw : HasUpperWitness d f r q frame U P) :
    ∃ D : MvPolynomial (Fin (finrank K (Space m d q f u (activeEvenIndices d)
      (targetLayerCount d h m r) (targetLayerOutput frame)))) K,
      (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 → Function.Surjective (upperTargetMap
        (enumerateForms (forms (by omega : 0<d)
          (fun j _ => targetLayerOutput_homogeneous frame j)
          (fun j hj => (activeEvenIndices_bounds hd hj).2.1.le)
          U P hP ((Module.finBasis K _).equivFun.symm a)))) := by
  obtain ⟨p,hzero,hlift⟩ := hw
  obtain ⟨D,hD,hgood⟩ := upper_target_open_of_literal_witness (by omega : 0<d)
    (fun j _ => targetLayerOutput_homogeneous frame j)
    (fun j hj => (activeEvenIndices_bounds hd hj).2.1.le) U P hP p hlift
  exact ⟨D,⟨(Module.finBasis K _).equivFun p,hD⟩,hgood⟩

theorem HasUpperWitness.exists_zero_private_rank_open (hd : 3≤d)
    (frame : Fin H → Forms K h 2) (U : Fin u → Forms K h d)
    (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K) (hP : ∀ i,(P i).IsHomogeneous d)
    (hw : HasUpperWitness d f r q frame U P) :
    ∃ D : MvPolynomial (Fin (finrank K (PreparedParameters.Space m d q (activeEvenIndices d)
      (targetLayerCount d h m r) (targetLayerOutput frame) × OuterSpace K (Fin h) m d f))) K,
      (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 → Function.Surjective (upperTargetMap
        (enumerateForms (forms (by omega : 0<d)
          (fun j _ => targetLayerOutput_homogeneous frame j)
          (fun j hj => (activeEvenIndices_bounds hd hj).2.1.le)
          U P hP (zeroPrivateScalar ((Module.finBasis K _).equivFun.symm a))))) := by
  obtain ⟨p,hzero,hlift⟩ := hw
  let v₀ := (p.1,p.2.1)
  have hv : zeroPrivateScalar v₀=p := by
    refine Prod.ext ?_ ?_
    · rfl
    · refine Prod.ext ?_ ?_
      · rfl
      · exact hzero.symm
  have hlift' : ∀ b,2≤b → b≤2*d → TargetLift
      ((Submodule.span K (Set.range (renamedGenerator U P (zeroPrivateScalar v₀))))*Forms K (h+m) d) d b := by
    simpa only [hv] using hlift
  obtain ⟨D,hD,hgood⟩ := upper_target_open_linear_of_literal_witness zeroPrivateScalar
    (by omega : 0<d) (fun j _ => targetLayerOutput_homogeneous frame j)
    (fun j hj => (activeEvenIndices_bounds hd hj).2.1.le) U P hP v₀ hlift'
  exact ⟨D,⟨(Module.finBasis K _).equivFun v₀,hD⟩,hgood⟩

end Froberg.PreparedTarget
