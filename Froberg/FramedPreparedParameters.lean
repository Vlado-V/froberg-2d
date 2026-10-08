import Froberg.OutputFrameFamily
import Froberg.CoreBiform
import Froberg.PreparedParameters

/-! The output-frame parameterization used for target surjectivity is the
full constrained biform parameter space used for prepared generators. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K] {h m j e H r : ℕ}
attribute [local instance] tensorGroup

def outputFrameSpace (frame : Fin H → Forms K h j) : Submodule K (Poly K h) :=
  Submodule.span K (Set.range (fun a => (frame a).val))

theorem outputFrameSpace_homogeneous (frame : Fin H → Forms K h j) :
    outputFrameSpace frame≤Forms K h j := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a,rfl⟩
  exact (frame a).property

theorem outputFrameSpace_finrank (frame : Fin H → Forms K h j)
    (hframe : LinearIndependent K frame) : finrank K (outputFrameSpace frame)=H := by
  have hi : LinearIndependent K (fun a => (frame a).val) :=
    hframe.map' (Forms K h j).subtype (Submodule.ker_subtype _)
  simpa only [outputFrameSpace,Fintype.card_fin] using finrank_span_eq_card hi

/-- An output frame gives all allowed coefficients of the prepared family;
there is no decomposability restriction on its entries. -/
theorem outputFrame_coefficients_surjective (frame : Fin H → Forms K h j)
    (hframe : LinearIndependent K frame) :
    (polynomialFormVector (n := m) (fun a => (frame a).val) e).range=
      biformImage (outputFrameSpace frame) (Forms K m e) := by
  have hi : LinearIndependent K (fun a => (frame a).val) :=
    hframe.map' (Forms K h j).subtype (Submodule.ker_subtype _)
  have hh := polynomialFormVector_range_basis (n := m) (s := e)
    (outputFrameSpace frame) (Basis.span hi)
  have hb : (fun i => ((Basis.span hi) i).val) = (fun i => (frame i).val) := by
    funext i
    exact Basis.coe_span_apply hi i
  have hmap := congrArg (fun o : Fin H → Poly K h =>
    (polynomialFormVector (n := m) o e).range) hb
  exact hmap.symm.trans hh

/-- The same frame-coefficient expression in sum-indexed polynomial
variables, matching PreparedParameters.Space exactly. -/
def sumBiform : (Forms K h j ⊗[K] Forms K m e) →ₗ[K]
    MvPolynomial (Fin h ⊕ Fin m) K :=
  (tensorEquivSum K (Fin h) (Fin m) K).toLinearMap.comp
    (TensorProduct.map (Forms K h j).subtype (Forms K m e).subtype)

theorem sumBiform_injective : Function.Injective
    (sumBiform (K := K) (h := h) (m := m) (j := j) (e := e)) :=
  (tensorEquivSum K (Fin h) (Fin m) K).injective.comp
    (TensorProduct.map_injective_of_flat_flat _ _
      (Forms K h j).injective_subtype (Forms K m e).injective_subtype)

theorem sumBiform_range :
    (sumBiform (K := K) (h := h) (m := m) (j := j) (e := e)).range=
      biformImage (Forms K h j) (Forms K m e) := by
  rw [sumBiform,LinearMap.range_comp]
  rfl

def sumBiformEquiv : (Forms K h j ⊗[K] Forms K m e) ≃ₗ[K]
    biformImage (Forms K h j) (Forms K m e) :=
  (LinearEquiv.ofInjective sumBiform sumBiform_injective).trans
    (LinearEquiv.ofEq _ _ sumBiform_range)

@[simp] theorem sumBiformEquiv_val (u : Forms K h j ⊗[K] Forms K m e) :
    (sumBiformEquiv u).val=sumBiform u := rfl

theorem rename_sumBiform (u : Forms K h j ⊗[K] Forms K m e) :
    rename finSumFinEquiv (sumBiform u)=ambientBiform u := by
  rw [ambientBiform_eq_split]
  rfl

@[simp] theorem sumBiform_tmul (a : Forms K h j) (b : Forms K m e) :
    sumBiform (a ⊗ₜ[K] b)=rename Sum.inl a.val*rename Sum.inr b.val := by
  simp only [sumBiform,LinearMap.comp_apply,TensorProduct.map_tmul,Submodule.subtype_apply,
    AlgEquiv.toLinearMap_apply,tensorEquivSum_tmul]

theorem sumBiform_framed (frame : Fin H → Forms K h j)
    (c : Fin r → Fin H → Forms K m e) (i : Fin r) :
    sumBiform (framedBiformFamily frame c i)=
      polynomialFormVector (n := m) (fun a => (frame a).val) e (c i) := by
  simp only [framedBiformFamily_apply,map_sum,sumBiform_tmul,polynomialFormVector_apply,polynomialVector_apply]

theorem framed_coefficients_mem_prepared (frame : Fin H → Forms K h j)
    (c : Fin r → Fin H → Forms K m e) (i : Fin r) :
    sumBiform (framedBiformFamily frame c i)∈biformImage (outputFrameSpace frame) (Forms K m e) := by
  rw [sumBiform_framed]
  apply polynomialFormVector_mem_biform
  · intro a
    exact Submodule.subset_span ⟨a,rfl⟩
  · intro a
    exact (c i a).property

end Froberg
