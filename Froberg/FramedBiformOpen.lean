module

public import Froberg.OutputFrameFamily
public import Froberg.PolynomialProperties

@[expose] public section

/-! Common output-plane and coefficient opens for several target rows. -/
noncomputable section
namespace Froberg
open Module TensorProduct MvPolynomial Quartic
open scoped BigOperators
variable {K : Type*} [Field K] [Infinite K]
variable {h m j e H r x y : ℕ}
attribute [local instance] tensorGroup

/-- An actual successful row in one H-plane gives a nonempty polynomial
open of H-frames where that row still has a successful coefficient family. -/
theorem framed_biform_row_base_open
    (W : Submodule K (Forms K h j)) (hW : finrank K W=H)
    (o : Fin r → W) (f : Fin r → Forms K m e)
    (hs : Function.Surjective (biformFamilyMap (x := x) (y := y) (fun i => (o i).val) f)) :
    ∃ D : MvPolynomial (Fin (finrank K (Fin H → Forms K h j))) K,
      (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 →
        LinearIndependent K ((Module.finBasis K (Fin H → Forms K h j)).equivFun.symm a) ∧
        ∃ c : Fin r → Fin H → Forms K m e,
          Function.Surjective (biformTensorFamilyMap (x := x) (y := y)
            (framedBiformFamily ((Module.finBasis K _).equivFun.symm a) c)) := by
  obtain ⟨frame,c,hframe,_,hc⟩ := exists_output_frame_lift W hW o f
  let a₀ := (Module.finBasis K (Fin H → Forms K h j)).equivFun frame
  have hrow : Function.Surjective (biformTensorFamilyMap (x := x) (y := y)
      (framedBiformFamily ((Module.finBasis K _).equivFun.symm a₀) c)) := by
    simpa only [a₀,LinearEquiv.symm_apply_apply,hc,biformTensorFamilyMap_pure] using hs
  obtain ⟨D,hD,hgood⟩ := biformTensorFamily_surjective_principal_open
    (fun a => framedBiformFamily ((Module.finBasis K _).equivFun.symm a) c)
    (framedBiformFamily_polynomial_frame c) a₀ hrow
  have hpoly (i : Fin H) : IsPolynomialFamily (fun a : Fin (finrank K (Fin H → Forms K h j)) → K =>
      (Module.finBasis K (Fin H → Forms K h j)).equivFun.symm a i) :=
    isPolynomialFamily_linear
      ((LinearMap.proj i : (Fin H → Forms K h j) →ₗ[K] Forms K h j).comp
        (Module.finBasis K (Fin H → Forms K h j)).equivFun.symm.toLinearMap)
  obtain ⟨E,hE,hind⟩ := independent_polynomial_principal_open
    (fun i a => (Module.finBasis K (Fin H → Forms K h j)).equivFun.symm a i)
    hpoly a₀ (by simpa only [a₀,LinearEquiv.symm_apply_apply] using hframe)
  refine ⟨D*E,⟨a₀,by simpa only [map_mul] using mul_ne_zero hD hE⟩,?_⟩
  intro a ha
  have hh : eval a D≠0 ∧ eval a E≠0 := by simpa only [map_mul,mul_ne_zero_iff] using ha
  exact ⟨hind a hh.2,c,hgood a hh.1⟩

/-- All target-row conditions share one output plane and, inside that plane,
one coefficient family. Each initial witness may have used a different plane. -/
theorem framed_biform_rows_common_open {J : Type*} [Fintype J] [Nonempty J]
    (x y : J → ℕ)
    (hwit : ∀ i,∃ (W : Submodule K (Forms K h j)) (o : Fin r → W)
      (f : Fin r → Forms K m e), finrank K W=H ∧
        Function.Surjective (biformFamilyMap (x := x i) (y := y i) (fun a => (o a).val) f)) :
    ∃ D : MvPolynomial (Fin (finrank K (Fin H → Forms K h j))) K,
      (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 →
        LinearIndependent K ((Module.finBasis K (Fin H → Forms K h j)).equivFun.symm a) ∧
        ∃ E : MvPolynomial (Fin (finrank K (Fin r → Fin H → Forms K m e))) K,
          (∃ c,eval c E≠0) ∧ ∀ c,eval c E≠0 → ∀ i,
            Function.Surjective (biformTensorFamilyMap (x := x i) (y := y i)
              (framedBiformFamily ((Module.finBasis K _).equivFun.symm a)
                ((Module.finBasis K _).equivFun.symm c))) := by
  classical
  let P (i : J) (a : Fin (finrank K (Fin H → Forms K h j)) → K) : Prop :=
    LinearIndependent K ((Module.finBasis K (Fin H → Forms K h j)).equivFun.symm a) ∧
      ∃ c : Fin r → Fin H → Forms K m e,
        Function.Surjective (biformTensorFamilyMap (x := x i) (y := y i)
          (framedBiformFamily ((Module.finBasis K _).equivFun.symm a) c))
  have hrow (i : J) : ∃ D : MvPolynomial (Fin (finrank K (Fin H → Forms K h j))) K,
      (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 → P i a := by
    obtain ⟨W,o,f,hW,hs⟩ := hwit i
    exact framed_biform_row_base_open W hW o f hs
  obtain ⟨D,hD,hgood⟩ := principal_property_common_open P hrow
  refine ⟨D,hD,fun a ha => ⟨(hgood a ha (Classical.arbitrary J)).1,?_⟩⟩
  apply surjective_polynomial_common_open
    (fun i c => biformTensorFamilyMap (x := x i) (y := y i)
      (framedBiformFamily ((Module.finBasis K _).equivFun.symm a)
        ((Module.finBasis K _).equivFun.symm c)))
  · intro i
    exact (framedBiformFamily_polynomial_coefficients _).linear_comp
      (biformTensorFamilyMap (x := x i) (y := y i))
  · intro i
    obtain ⟨c,hc⟩ := (hgood a ha i).2
    refine ⟨(Module.finBasis K _).equivFun c,?_⟩
    simpa only [LinearEquiv.symm_apply_apply] using hc

end Froberg
