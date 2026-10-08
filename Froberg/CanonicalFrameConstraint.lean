import Froberg.PrivateFrameConstraints
import Froberg.TargetLayerAssembly
import Froberg.QuadraticOutputDimension

/-! A quadratic frame is exactly the kernel constraint required by the
actual even-row construction. This detector uses its ordinary quotient. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h H : ℕ}

def frameQuotientDimension (frame : Fin H → Forms K h 2) : ℕ :=
  finrank K (Forms K h 2 ⧸ Submodule.span K (Set.range frame))

def canonicalFrameDetector (frame : Fin H → Forms K h 2) :
    Forms K h 2 →ₗ[K] (Fin (frameQuotientDimension frame) → K) :=
  (Module.finBasis K (Forms K h 2 ⧸ Submodule.span K (Set.range frame))).equivFun.toLinearMap.comp
    (Submodule.span K (Set.range frame)).mkQ

theorem canonicalFrameDetector_kernel (frame : Fin H → Forms K h 2) :
    (canonicalFrameDetector frame).ker=Submodule.span K (Set.range frame) := by
  ext x
  change (Module.finBasis K _).equivFun ((Submodule.span K (Set.range frame)).mkQ x)=0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]

def canonicalFrameConstraint (frame : Fin H → Forms K h 2) (j : ℕ) :
    Poly K h →ₗ[K] (Fin (frameQuotientDimension frame) → K) :=
  if j=2 then quadraticPolynomialDetector (canonicalFrameDetector frame) else 0

theorem canonicalFrameConstraint_outputs (frame : Fin H → Forms K h 2) (j : ℕ) :
    Forms K h j ⊓ (canonicalFrameConstraint frame j).ker=targetLayerOutput frame j := by
  by_cases hj : j=2
  · subst j
    simpa only [canonicalFrameConstraint,targetLayerOutput,ite_true] using
      quadratic_detector_homogeneous_kernel frame _ (canonicalFrameDetector_kernel frame)
  · simp only [canonicalFrameConstraint,targetLayerOutput,if_neg hj,LinearMap.ker_zero,inf_top_eq]

theorem canonicalFrameConstraint_ge_four (frame : Fin H → Forms K h 2)
    {j : ℕ} (hj : 4≤j) : canonicalFrameConstraint frame j=0 := by
  simp only [canonicalFrameConstraint,if_neg (show j≠2 by omega)]

theorem canonicalFrameConstraint_dimension {d : ℕ} (hh : 0<h)
    (hcolumn : outerColumnCount d h≤h)
    (frame : Fin (quadraticOutputDimension d h) → Forms K h 2)
    (hframe : LinearIndependent K frame) :
    frameQuotientDimension frame=deletedTargetCount d h := by
  have hdel : deletedTargetCount d h≤(h+1).choose 2 :=
    Nat.choose_le_choose 2 (Nat.add_le_add_right hcolumn 1)
  rw [frameQuotientDimension,quadratic_frame_quotient_finrank frame hframe,finrank_forms K h 2 hh]
  simp only [quadraticOutputDimension,show h+2-1=h+1 by omega]
  exact Nat.sub_sub_self hdel

end Froberg
