module

public import Froberg.FullPreparedFibers
public import Froberg.UpperTargetOpen

@[expose] public section

/-! Rank openness is applied to the actual varying family. In particular,
a successful fixed private tuple gives a nonempty open with variable
private parts, including on the fixed-pure, zero-scalar odd fiber. -/
noncomputable section
namespace Froberg.FullPreparedParameters
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem upper_target_open_affine {V : Type*}
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (p₀ : Space m d q f u J counts O) (L : V →ₗ[K] Space m d q f u J counts O)
    (hd : 0 < d) (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (v₀ : V) (hw : Function.Surjective (upperTargetMap
      (PreparedTarget.enumerateForms (forms hd hO hJ (p₀+L v₀))))) :
    ∃ D : MvPolynomial (Fin (finrank K V)) K,
      eval ((Module.finBasis K V).equivFun v₀) D≠0 ∧
      ∀ a,eval a D≠0 → Function.Surjective (upperTargetMap
        (PreparedTarget.enumerateForms (forms hd hO hJ
          (p₀+L ((Module.finBasis K V).equivFun.symm a))))) := by
  apply upperTarget_principal_open _
    (enumerated_forms_polynomial_affine_parameters p₀ L hd hO hJ)
    ((Module.finBasis K V).equivFun v₀)
  simpa only [LinearEquiv.symm_apply_apply] using hw

theorem upper_target_open_fixed_pure
    [Module.Finite K (FixedPureSpace m d q f u J counts O)]
    (hd : 0 < d) (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (U : Fin u → Forms K h d) (P : PreparedTarget.OuterSpace K (Fin h) m d u)
    (p : PreparedTarget.Space m d q f u J counts O)
    (hw : Function.Surjective (upperTargetMap
      (PreparedTarget.enumerateForms (PreparedTarget.forms hd hO hJ U
        (fun i => (P i).val) (private_homogeneous hd P) p)))) :
    ∃ D : MvPolynomial (Fin (finrank K (FixedPureSpace m d q f u J counts O))) K,
      eval ((Module.finBasis K _).equivFun (P,p)) D≠0 ∧
      ∀ a,eval a D≠0 → Function.Surjective (upperTargetMap
        (PreparedTarget.enumerateForms (forms hd hO hJ
          (pureBase U+variablePrivate ((Module.finBasis K _).equivFun.symm a))))) := by
  apply upper_target_open_affine (pureBase U) variablePrivate hd hO hJ (P,p)
  simpa only [pureBase_add_variablePrivate,forms_eq_fixed] using hw

theorem upper_target_open_fixed_pure_zero_scalar
    [Module.Finite K (FixedPureZeroScalarSpace m d q f u J counts O)]
    (hd : 0 < d) (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (U : Fin u → Forms K h d) (P : PreparedTarget.OuterSpace K (Fin h) m d u)
    (p : PreparedParameters.Space m d q J counts O × PreparedTarget.OuterSpace K (Fin h) m d f)
    (hw : Function.Surjective (upperTargetMap
      (PreparedTarget.enumerateForms (PreparedTarget.forms hd hO hJ U
        (fun i => (P i).val) (private_homogeneous hd P) (PreparedTarget.zeroPrivateScalar p))))) :
    ∃ D : MvPolynomial (Fin (finrank K (FixedPureZeroScalarSpace m d q f u J counts O))) K,
      eval ((Module.finBasis K _).equivFun (P,p)) D≠0 ∧
      ∀ a,eval a D≠0 → Function.Surjective (upperTargetMap
        (PreparedTarget.enumerateForms (forms hd hO hJ
          (pureBase U+variablePrivateZeroScalar ((Module.finBasis K _).equivFun.symm a))))) := by
  apply upper_target_open_affine (pureBase U) variablePrivateZeroScalar hd hO hJ (P,p)
  simpa only [pureBase_add_variablePrivateZeroScalar,forms_eq_fixed] using hw

end Froberg.FullPreparedParameters
