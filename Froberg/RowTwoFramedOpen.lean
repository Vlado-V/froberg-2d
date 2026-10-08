import Froberg.FramedBiformOpen
import Froberg.BiformPairOpen

/-! The row-two witness as an open condition on an output frame. This
uses the same affine frame parameters as rows three and four. -/
noncomputable section
namespace Froberg
open Module TensorProduct MvPolynomial Quartic
variable {K : Type*} [Field K] [Infinite K]
variable {h m s e y H r q : ℕ}
attribute [local instance] tensorGroup

theorem row_two_framed_base_open
    (W : Submodule K (Forms K h 2)) (hW : finrank K W=H)
    (o : Fin r → Forms K h 1) (f : Fin r → Forms K m s)
    (O : Fin q → W) (g : Fin q → Forms K m e) (he : e+y=s+s)
    (hs : Function.Surjective ((biformFamilyMap (x := 1) (y := s) o f).coprod
      (vectorFormFamilyToDegree he (fun i => (O i).val) g))) :
    ∃ D : MvPolynomial (Fin (finrank K (Fin H → Forms K h 2))) K,
      (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 →
        LinearIndependent K ((Module.finBasis K (Fin H → Forms K h 2)).equivFun.symm a) ∧
        ∃ (F : Fin r → Forms K h 1 ⊗[K] Forms K m s)
          (c : Fin q → Fin H → Forms K m e),
          Function.Surjective ((biformTensorFamilyMap (x := 1) (y := s) F).coprod
            (biformTensorFamilyToDegree (x := 0) he
              (framedBiformFamily ((Module.finBasis K _).equivFun.symm a) c))) := by
  obtain ⟨frame,c,hframe,_,hc⟩ := exists_output_frame_lift W hW O g
  let a₀ := (Module.finBasis K (Fin H → Forms K h 2)).equivFun frame
  let F : Fin r → Forms K h 1 ⊗[K] Forms K m s := fun i => o i ⊗ₜ[K] f i
  have hrow : Function.Surjective ((biformTensorFamilyMap (x := 1) (y := s) F).coprod
      (biformTensorFamilyToDegree (x := 0) he
        (framedBiformFamily ((Module.finBasis K _).equivFun.symm a₀) c))) := by
    simpa only [a₀,LinearEquiv.symm_apply_apply,hc,F] using
      row_two_full_surjective o f (fun i => (O i).val) g he hs
  obtain ⟨D,hD,hgood⟩ := row_two_full_principal_open (fun _ => F)
    (fun a => framedBiformFamily ((Module.finBasis K _).equivFun.symm a) c)
    (isPolynomialFamily_const F) (framedBiformFamily_polynomial_frame c) he a₀ hrow
  have hpoly (i : Fin H) : IsPolynomialFamily (fun a : Fin (finrank K (Fin H → Forms K h 2)) → K =>
      (Module.finBasis K (Fin H → Forms K h 2)).equivFun.symm a i) :=
    isPolynomialFamily_linear
      ((LinearMap.proj i : (Fin H → Forms K h 2) →ₗ[K] Forms K h 2).comp
        (Module.finBasis K (Fin H → Forms K h 2)).equivFun.symm.toLinearMap)
  obtain ⟨E,hE,hind⟩ := independent_polynomial_principal_open
    (fun i a => (Module.finBasis K (Fin H → Forms K h 2)).equivFun.symm a i)
    hpoly a₀ (by simpa only [a₀,LinearEquiv.symm_apply_apply] using hframe)
  refine ⟨D*E,⟨a₀,by simpa only [map_mul] using mul_ne_zero hD hE⟩,?_⟩
  intro a ha
  have hh : eval a D≠0 ∧ eval a E≠0 := by simpa only [map_mul,mul_ne_zero_iff] using ha
  exact ⟨hind a hh.2,F,c,hgood a hh.1⟩

end Froberg
