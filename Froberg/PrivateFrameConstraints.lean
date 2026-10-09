module

public import Froberg.PrivateDetectorRename
public import Froberg.PreparedFiniteRows

@[expose] public section

/-! A general quadratic frame determines exactly the constrained paired
output spaces used by the finite private-row construction. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial PrivateColumns PreparedParameters
variable {K : Type} [Field K] [Infinite K]
variable {w h H c : ℕ}

theorem quadratic_detector_homogeneous_kernel
    (frame : Fin H → Forms K h 2)
    (L : Forms K h 2 →ₗ[K] (Fin c → K))
    (hL : L.ker=Submodule.span K (Set.range frame)) :
    Forms K h 2 ⊓ (quadraticPolynomialDetector L).ker=outputFrameSpace frame := by
  have hspan : (Submodule.span K (Set.range frame)).map (Forms K h 2).subtype=
      outputFrameSpace frame := by
    rw [Submodule.map_span]
    rw [←Set.range_comp]
    rfl
  apply le_antisymm
  · intro p hp
    rw [←hspan]
    refine ⟨⟨p,hp.1⟩,?_,rfl⟩
    rw [←hL]
    change L ⟨p,hp.1⟩=0
    rw [←quadraticPolynomialDetector_form L ⟨p,hp.1⟩]
    exact hp.2
  · exact le_inf (outputFrameSpace_homogeneous frame) (quadraticPolynomialDetector_frame frame L hL)

def pairedFrameConstraint (f : (Fin w × Bool) ≃ Fin h)
    (L : Forms K h 2 →ₗ[K] (Fin c → K)) (j : ℕ) :
    MvPolynomial (Fin w × Bool) K →ₗ[K] (Fin c → K) :=
  if j=2 then (quadraticPolynomialDetector L).comp (rename f).toLinearMap else 0

@[simp] theorem pairedFrameConstraint_two (f : (Fin w × Bool) ≃ Fin h)
    (L : Forms K h 2 →ₗ[K] (Fin c → K)) :
    pairedFrameConstraint f L 2=(quadraticPolynomialDetector L).comp (rename f).toLinearMap := by
  simp only [pairedFrameConstraint,ite_true]

theorem pairedFrameConstraint_ne_two (f : (Fin w × Bool) ≃ Fin h)
    (L : Forms K h 2 →ₗ[K] (Fin c → K)) {j : ℕ} (hj : j≠2) :
    pairedFrameConstraint f L j=0 := by
  simp only [pairedFrameConstraint,if_neg hj]

theorem pairedFrameConstraint_ge_four (f : (Fin w × Bool) ≃ Fin h)
    (L : Forms K h 2 →ₗ[K] (Fin c → K)) {j : ℕ} (hj : 4≤j) :
    pairedFrameConstraint f L j=0 := pairedFrameConstraint_ne_two f L (by omega)

theorem pairedFrameConstraint_space (f : (Fin w × Bool) ≃ Fin h)
    (frame : Fin H → Forms K h 2)
    (L : Forms K h 2 →ₗ[K] (Fin c → K))
    (hL : L.ker=Submodule.span K (Set.range frame)) :
    constrainedOutputs (pairedFrameConstraint f L) 2=
      (outputFrameSpace frame).comap (rename f).toLinearMap := by
  ext p
  change (p.IsHomogeneous 2 ∧ pairedFrameConstraint f L 2 p=0) ↔
    rename f p∈outputFrameSpace frame
  rw [←quadratic_detector_homogeneous_kernel frame L hL]
  change (p.IsHomogeneous 2 ∧ pairedFrameConstraint f L 2 p=0) ↔
    ((rename f p).IsHomogeneous 2 ∧ quadraticPolynomialDetector L (rename f p)=0)
  rw [pairedFrameConstraint_two,LinearMap.comp_apply,AlgHom.toLinearMap_apply]
  constructor
  · rintro ⟨hp,hzero⟩
    exact ⟨hp.rename_isHomogeneous,hzero⟩
  · rintro ⟨hp,hzero⟩
    refine ⟨?_,hzero⟩
    have hh := hp.rename_isHomogeneous (f := f.symm)
    simpa only [rename_rename,Equiv.symm_comp_self,rename_id_apply] using hh

theorem pairedFrameConstraint_space_map (f : (Fin w × Bool) ≃ Fin h)
    (frame : Fin H → Forms K h 2)
    (L : Forms K h 2 →ₗ[K] (Fin c → K))
    (hL : L.ker=Submodule.span K (Set.range frame)) :
    (constrainedOutputs (pairedFrameConstraint f L) 2).map (rename f).toLinearMap=
      outputFrameSpace frame := by
  rw [pairedFrameConstraint_space f frame L hL]
  exact Submodule.map_comap_eq_of_surjective ((renameEquiv K f).surjective) _

theorem pairedFrameConstraint_space_map_ne_two (f : (Fin w × Bool) ≃ Fin h)
    (L : Forms K h 2 →ₗ[K] (Fin c → K)) {j : ℕ} (hj : j≠2) :
    (constrainedOutputs (pairedFrameConstraint f L) j).map (rename f).toLinearMap=
      Forms K h j := by
  rw [constrainedOutputs,pairedFrameConstraint_ne_two f L hj,LinearMap.ker_zero,inf_top_eq]
  apply le_antisymm
  · rintro _ ⟨p,hp,rfl⟩
    exact hp.rename_isHomogeneous
  · intro p hp
    refine ⟨rename f.symm p,hp.rename_isHomogeneous,?_⟩
    exact (renameEquiv K f).right_inv p

theorem pairedFrameConstraint_spaces_map (f : (Fin w × Bool) ≃ Fin h)
    (frame : Fin H → Forms K h 2)
    (L : Forms K h 2 →ₗ[K] (Fin c → K))
    (hL : L.ker=Submodule.span K (Set.range frame)) (j : ℕ) :
    (constrainedOutputs (pairedFrameConstraint f L) j).map (rename f).toLinearMap=
      if j=2 then outputFrameSpace frame else Forms K h j := by
  by_cases hj : j=2
  · subst j
    simpa only [ite_true] using pairedFrameConstraint_space_map f frame L hL
  · simpa only [if_neg hj] using pairedFrameConstraint_space_map_ne_two f L hj

theorem pairedFrameConstraint_space_finrank (f : (Fin w × Bool) ≃ Fin h)
    (frame : Fin H → Forms K h 2) (hframe : LinearIndependent K frame)
    (L : Forms K h 2 →ₗ[K] (Fin c → K))
    (hL : L.ker=Submodule.span K (Set.range frame)) :
    finrank K (constrainedOutputs (pairedFrameConstraint f L) 2)=H := by
  have hh := (renameEquiv K f).toLinearEquiv.finrank_map_eq
    (constrainedOutputs (pairedFrameConstraint f L) 2)
  change finrank K ((constrainedOutputs (pairedFrameConstraint f L) 2).map
    (rename f).toLinearMap)=finrank K (constrainedOutputs (pairedFrameConstraint f L) 2) at hh
  rw [pairedFrameConstraint_space_map f frame L hL] at hh
  exact hh.symm.trans (outputFrameSpace_finrank frame hframe)

theorem quadratic_frame_quotient_finrank
    (frame : Fin H → Forms K h 2) (hframe : LinearIndependent K frame) :
    finrank K (Forms K h 2 ⧸ Submodule.span K (Set.range frame))=
      finrank K (Forms K h 2)-H := by
  have hdim : finrank K (Submodule.span K (Set.range frame))=H := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hframe
  have hh := (Submodule.span K (Set.range frame)).finrank_quotient_add_finrank
  rw [hdim] at hh
  omega

end Froberg
