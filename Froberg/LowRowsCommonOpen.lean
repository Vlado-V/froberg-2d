import Froberg.RowTwoFramedOpen
import Froberg.PolynomialBinaryOpen

/-! Rows two, three and four simultaneously in one quadratic output plane.
Separate witnesses yield a nonempty frame open, then a nonempty common
coefficient open in every such frame. -/
noncomputable section
namespace Froberg
open Module TensorProduct MvPolynomial Quartic
variable {K : Type*} [Field K] [Infinite K]
variable {h m s e y H r q : ℕ}
attribute [local instance] tensorGroup

abbrev LowRowCoefficients (K : Type*) [Field K] (h m s e H r q : ℕ) :=
  (Fin r → Forms K h 1 ⊗[K] Forms K m s) × (Fin q → Fin H → Forms K m e)

def LowRowsSurjective (he : e+y=s+s) (frame : Fin H → Forms K h 2)
    (p : LowRowCoefficients K h m s e H r q) : Prop :=
  Function.Surjective ((biformTensorFamilyMap (x := 1) (y := s) p.1).coprod
    (biformTensorFamilyToDegree (x := 0) he (framedBiformFamily frame p.2))) ∧
  Function.Surjective (biformTensorFamilyMap (x := 1) (y := s) (framedBiformFamily frame p.2)) ∧
  Function.Surjective (biformTensorFamilyMap (x := 2) (y := e) (framedBiformFamily frame p.2))

theorem low_rows_common_coefficient_open (he : e+y=s+s) (frame : Fin H → Forms K h 2)
    (h₂ : ∃ (F : Fin r → Forms K h 1 ⊗[K] Forms K m s) (c : Fin q → Fin H → Forms K m e),
      Function.Surjective ((biformTensorFamilyMap (x := 1) (y := s) F).coprod
        (biformTensorFamilyToDegree (x := 0) he (framedBiformFamily frame c))))
    (h₃ : ∃ c : Fin q → Fin H → Forms K m e,
      Function.Surjective (biformTensorFamilyMap (x := 1) (y := s) (framedBiformFamily frame c)))
    (h₄ : ∃ c : Fin q → Fin H → Forms K m e,
      Function.Surjective (biformTensorFamilyMap (x := 2) (y := e) (framedBiformFamily frame c))) :
    ∃ D : MvPolynomial (Fin (finrank K (LowRowCoefficients K h m s e H r q))) K,
      (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 →
        LowRowsSurjective he frame ((Module.finBasis K _).equivFun.symm a) := by
  let B := (Module.finBasis K (LowRowCoefficients K h m s e H r q)).equivFun
  let F := (LinearMap.fst K (Fin r → Forms K h 1 ⊗[K] Forms K m s)
    (Fin q → Fin H → Forms K m e)).comp B.symm.toLinearMap
  let E := (framedBiformFamily frame).comp
    ((LinearMap.snd K (Fin r → Forms K h 1 ⊗[K] Forms K m s)
      (Fin q → Fin H → Forms K m e)).comp B.symm.toLinearMap)
  have hF : IsPolynomialFamily F := isPolynomialFamily_linear F
  have hE : IsPolynomialFamily E := isPolynomialFamily_linear E
  obtain ⟨F₂,c₂,h₂⟩ := h₂
  obtain ⟨c₃,h₃⟩ := h₃
  obtain ⟨c₄,h₄⟩ := h₄
  have hs₂ : Function.Surjective ((biformTensorFamilyMap (x := 1) (y := s) (F (B (F₂,c₂)))).coprod
      (biformTensorFamilyToDegree (x := 0) he (E (B (F₂,c₂))))) := by
    simpa only [F,E,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,
      LinearMap.fst_apply,LinearMap.snd_apply] using h₂
  obtain ⟨D₂,hD₂,hgood₂⟩ := row_two_full_principal_open F E hF hE he (B (F₂,c₂)) hs₂
  have hs₃ : Function.Surjective (biformTensorFamilyMap (x := 1) (y := s) (E (B (0,c₃)))) := by
    simpa only [E,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,
      LinearMap.snd_apply] using h₃
  obtain ⟨D₃,hD₃,hgood₃⟩ := biformTensorFamily_surjective_principal_open E hE (B (0,c₃)) hs₃
  have hs₄ : Function.Surjective (biformTensorFamilyMap (x := 2) (y := e) (E (B (0,c₄)))) := by
    simpa only [E,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,
      LinearMap.snd_apply] using h₄
  obtain ⟨D₄,hD₄,hgood₄⟩ := biformTensorFamily_surjective_principal_open E hE (B (0,c₄)) hs₄
  obtain ⟨D,hD,hgood⟩ := principal_property_inter
    ⟨D₂,⟨B (F₂,c₂),hD₂⟩,hgood₂⟩
    (principal_property_inter ⟨D₃,⟨B (0,c₃),hD₃⟩,hgood₃⟩ ⟨D₄,⟨B (0,c₄),hD₄⟩,hgood₄⟩)
  refine ⟨D,hD,?_⟩
  intro a ha
  exact hgood a ha


/-- The three low rows can be imposed on one output plane even though their
initial constructions choose different planes. -/
theorem low_rows_shared_frame_open (he : e+y=s+s)
    (h₂ : ∃ (o : Fin r → Forms K h 1) (f : Fin r → Forms K m s)
      (W : Submodule K (Forms K h 2)) (O : Fin q → W) (g : Fin q → Forms K m e),
      finrank K W=H ∧ Function.Surjective ((biformFamilyMap (x := 1) (y := s) o f).coprod
        (vectorFormFamilyToDegree he (fun i => (O i).val) g)))
    (h₃ : ∃ (W : Submodule K (Forms K h 2)) (o : Fin q → W) (f : Fin q → Forms K m e),
      finrank K W=H ∧ Function.Surjective (biformFamilyMap (x := 1) (y := s) (fun i => (o i).val) f))
    (h₄ : ∃ (W : Submodule K (Forms K h 2)) (o : Fin q → W) (f : Fin q → Forms K m e),
      finrank K W=H ∧ Function.Surjective (biformFamilyMap (x := 2) (y := e) (fun i => (o i).val) f)) :
    ∃ D : MvPolynomial (Fin (finrank K (Fin H → Forms K h 2))) K,
      (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 →
        LinearIndependent K ((Module.finBasis K (Fin H → Forms K h 2)).equivFun.symm a) ∧
        ∃ E : MvPolynomial (Fin (finrank K (LowRowCoefficients K h m s e H r q))) K,
          (∃ c,eval c E≠0) ∧ ∀ c,eval c E≠0 →
            LowRowsSurjective he ((Module.finBasis K _).equivFun.symm a)
              ((Module.finBasis K _).equivFun.symm c) := by
  obtain ⟨o₂,f₂,W₂,O₂,g₂,hW₂,hs₂⟩ := h₂
  obtain ⟨W₃,o₃,f₃,hW₃,hs₃⟩ := h₃
  obtain ⟨W₄,o₄,f₄,hW₄,hs₄⟩ := h₄
  obtain ⟨D,hD,hgood⟩ := principal_property_inter
    (row_two_framed_base_open W₂ hW₂ o₂ f₂ O₂ g₂ he hs₂)
    (principal_property_inter
      (framed_biform_row_base_open W₃ hW₃ o₃ f₃ hs₃)
      (framed_biform_row_base_open W₄ hW₄ o₄ f₄ hs₄))
  refine ⟨D,hD,?_⟩
  intro a ha
  have hh := hgood a ha
  refine ⟨hh.1.1,?_⟩
  exact low_rows_common_coefficient_open he _ hh.1.2 hh.2.1.2 hh.2.2.2

end Froberg
