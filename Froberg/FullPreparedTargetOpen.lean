import Froberg.FullPreparedRankOpen
import Froberg.PreparedTargetOpen

/-! The B.7 witness supplies a rank-open condition in the same variable
private-part family used by the odd exactness and outer-vector arguments. -/
noncomputable section
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [CharZero K] {h m d H f r q u : ℕ}

abbrev VariablePrivateTargetSpace (d m f r q u : ℕ) (frame : Fin H → Forms K h 2) :=
  FullPreparedParameters.FixedPureZeroScalarSpace m d q f u (activeEvenIndices d)
    (targetLayerCount d h m r) (targetLayerOutput frame)

local instance variablePrivateTargetFinite (frame : Fin H → Forms K h 2) :
    Module.Finite K (VariablePrivateTargetSpace d m f r q u frame) :=
  FullPreparedParameters.finite_fixedPureZeroScalarSpace
    (fun j _ => targetLayerOutput_homogeneous frame j)

def VariablePrivateUpperOpen (hd : 3≤d) (f r q : ℕ)
    (frame : Fin H → Forms K h 2) (U : Fin u → Forms K h d) : Prop :=
  ∃ D : MvPolynomial (Fin (finrank K (VariablePrivateTargetSpace d m f r q u frame))) K,
    (∃ p : VariablePrivateTargetSpace d m f r q u frame,
      eval ((Module.finBasis K _).equivFun p) D≠0) ∧
    ∀ p : VariablePrivateTargetSpace d m f r q u frame,
      eval ((Module.finBasis K _).equivFun p) D≠0 → Function.Surjective (upperTargetMap
        (enumerateForms (FullPreparedParameters.forms (by omega : 0<d)
          (fun j _ => targetLayerOutput_homogeneous frame j)
          (fun j hj => (activeEvenIndices_bounds hd hj).2.1.le)
          (FullPreparedParameters.pureBase U+
            FullPreparedParameters.variablePrivateZeroScalar p))))

theorem HasUpperWitness.variable_private_open (hd : 3≤d)
    (frame : Fin H → Forms K h 2) (U : Fin u → Forms K h d)
    (P : OuterSpace K (Fin h) m d u)
    (hw : HasUpperWitness d f r q frame U (fun i => (P i).val)) :
    VariablePrivateUpperOpen (m := m) hd f r q frame U := by
  obtain ⟨p,hzero,hp⟩ := hw.exists_upperTarget_surjective hd frame U
    (fun i => (P i).val) (FullPreparedParameters.private_homogeneous (by omega) P)
  let v := (p.1,p.2.1)
  have hv : zeroPrivateScalar v=p := by
    refine Prod.ext ?_ ?_
    · rfl
    · refine Prod.ext ?_ ?_
      · rfl
      · exact hzero.symm
  obtain ⟨D,hD,hgood⟩ := FullPreparedParameters.upper_target_open_fixed_pure_zero_scalar
    (by omega : 0<d) (fun j _ => targetLayerOutput_homogeneous frame j)
    (fun j hj => (activeEvenIndices_bounds hd hj).2.1.le) U P v
    (by simpa only [hv] using hp)
  refine ⟨D,⟨(P,v),hD⟩,?_⟩
  intro z hz
  simpa only [LinearEquiv.symm_apply_apply] using
    hgood ((Module.finBasis K _).equivFun z) hz

end Froberg.PreparedTarget
