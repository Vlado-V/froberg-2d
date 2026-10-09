module

public import Froberg.SubspaceFrame
public import Froberg.BiformTensorFamily
public import Froberg.SurjectiveParameterOpen
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

/-! Output frames parameterize constrained biform families by ordinary affine
coordinates. Every witness in a prescribed-dimensional output plane lifts to
this same parameter space. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module TensorProduct MvPolynomial Quartic
variable {K : Type*} [Field K] {h m j e H r : ℕ}

/-- One common output frame with unrestricted scalar coefficient forms. -/
def framedBiformFamily : (Fin H → Forms K h j) →ₗ[K]
    (Fin r → Fin H → Forms K m e) →ₗ[K]
      (Fin r → Forms K h j ⊗[K] Forms K m e) where
  toFun o :=
    { toFun := fun c i => ∑ a,o a ⊗ₜ[K] c i a
      map_add' := by
        intro c c'
        funext i
        simp only [Pi.add_apply,tmul_add,Finset.sum_add_distrib]
      map_smul' := by
        intro k c
        funext i
        simp only [Pi.smul_apply,tmul_smul,Finset.smul_sum,RingHom.id_apply] }
  map_add' o o' := by
    apply LinearMap.ext
    intro c
    funext i
    change (∑ a,(o+o') a ⊗ₜ[K] c i a)=(∑ a,o a ⊗ₜ[K] c i a)+(∑ a,o' a ⊗ₜ[K] c i a)
    simp only [Pi.add_apply,add_tmul,Finset.sum_add_distrib]
  map_smul' k o := by
    apply LinearMap.ext
    intro c
    funext i
    change (∑ a,(k • o) a ⊗ₜ[K] c i a)=k • (∑ a,o a ⊗ₜ[K] c i a)
    simp only [Pi.smul_apply,smul_tmul',Finset.smul_sum]

@[simp] theorem framedBiformFamily_apply (o : Fin H → Forms K h j)
    (c : Fin r → Fin H → Forms K m e) (i : Fin r) :
    framedBiformFamily o c i = ∑ a,o a ⊗ₜ[K] c i a := by
  simp [framedBiformFamily]

/-- Every pure-tensor witness in an H-dimensional output plane is a point
of the unrestricted frame/coefficient parameter space. The frame itself is
independent, so it represents a plane of exactly the prescribed dimension. -/
theorem exists_output_frame_lift (W : Submodule K (Forms K h j))
    (hW : finrank K W=H) (o : Fin r → W) (f : Fin r → Forms K m e) :
    ∃ (frame : Fin H → Forms K h j) (c : Fin r → Fin H → Forms K m e),
      LinearIndependent K frame ∧ Submodule.span K (Set.range frame)=W ∧
        framedBiformFamily frame c = fun i => (o i).val ⊗ₜ[K] f i := by
  classical
  obtain ⟨frame,c,hframe,hspan,hc⟩ := exists_subspace_frame W hW o
  refine ⟨frame,(fun i a => c i a • f i),hframe,hspan,?_⟩
  funext i
  rw [framedBiformFamily_apply]
  simp only [tmul_smul,smul_tmul']
  rw [←sum_tmul,hc]

attribute [local instance] tensorGroup

/-- Holding coefficient forms fixed makes the family polynomial in the
output frame, and holding the frame fixed makes it polynomial in coefficients. -/
theorem framedBiformFamily_polynomial_frame
    (c : Fin r → Fin H → Forms K m e) :
    IsPolynomialFamily (fun a : Fin (finrank K (Fin H → Forms K h j)) → K =>
      framedBiformFamily ((Module.finBasis K _).equivFun.symm a) c) := by
  exact isPolynomialFamily_linear
    (((framedBiformFamily (h := h) (m := m) (j := j) (e := e) (H := H) (r := r)).flip c).comp
      (Module.finBasis K (Fin H → Forms K h j)).equivFun.symm.toLinearMap)

theorem framedBiformFamily_polynomial_coefficients (frame : Fin H → Forms K h j) :
    IsPolynomialFamily (fun a : Fin (finrank K (Fin r → Fin H → Forms K m e)) → K =>
      framedBiformFamily frame ((Module.finBasis K _).equivFun.symm a)) := by
  exact isPolynomialFamily_linear
    ((framedBiformFamily frame).comp
      (Module.finBasis K (Fin r → Fin H → Forms K m e)).equivFun.symm.toLinearMap)

end Froberg
