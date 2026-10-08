import Froberg.PreparedJointCoordinates
import Froberg.HigherOddVectorOpen

/-! The actual outer tensor and base scalar families are independent
linear coordinates of the complete parameter space. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def preparedBaseProjection : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O →ₗ[K] OddScalarParameters K h m d f q :=
  scalarVectorParametersEquiv.toLinearMap.comp
    (((LinearMap.fst K _ _).prod ((LinearMap.fst K _ _).comp (LinearMap.snd K _ _))).comp
      preparedJointCoordinates.toLinearMap)

@[simp] theorem preparedBaseProjection_eval (p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :
    preparedBaseProjection p=(fun i => linearOutputTensorEquiv (PreparedTarget.outerVectorEquiv.symm (p.2.2 i)),
      fun i => p.2.1.1 (Sum.inl i)) := rfl

theorem preparedBaseProjection_surjective :
    Function.Surjective (preparedBaseProjection (m := m) (d := d) (q := q) (f := f) (u := u) (J := J) (counts := counts) (O := O)) := by
  intro y
  let x := (scalarVectorParametersEquiv (K := K) (h := h) (m := m) (d := d) (f := f) (q := q)).symm y
  let ec := preparedJointCoordinates (K := K) (h := h) (m := m) (d := d)
    (q := q) (f := f) (u := u) (J := J) (counts := counts) (O := O)
  refine ⟨ec.symm (x.1,x.2,0),?_⟩
  change scalarVectorParametersEquiv ((ec (ec.symm (x.1,x.2,0))).1,
    (ec (ec.symm (x.1,x.2,0))).2.1)=y
  rw [LinearEquiv.apply_symm_apply]
  exact scalarVectorParametersEquiv.apply_symm_apply y

theorem prepared_base_principal_pullback (hO : ∀ j∈J,O j≤Forms K h j)
    (D : MvPolynomial (Fin (finrank K (OddScalarParameters K h m d f q))) K)
    (hD : ∃ p : OddScalarParameters K h m d f q,eval ((Module.finBasis K _).equivFun p) D≠0)
    (Good : OddScalarParameters K h m d f q → Prop)
    (hGood : ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 → Good p) :
    letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
    ∃ P : MvPolynomial (Fin (finrank K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O))) K,
      (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,eval ((Module.finBasis K _).equivFun p) P≠0) ∧
      ∀ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,eval ((Module.finBasis K _).equivFun p) P≠0 → Good (preparedBaseProjection p) := by
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  exact principal_open_linear_pullback preparedBaseProjection preparedBaseProjection_surjective D hD Good hGood

end Froberg.PreparedParameters
