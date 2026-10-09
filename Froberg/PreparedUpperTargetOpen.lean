module

public import Froberg.PreparedTargetForms
public import Froberg.UpperTargetOpen

@[expose] public section

/-! The high-target rank open in exactly the full prepared parameter space,
including arbitrary scalar shifts and the complete outer biform family. -/
noncomputable section
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem upper_target_open_of_witness (hd : 0<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    [Module.Finite K (Space m d q f u J counts O)]
    (U : Fin u → Forms K h d)
    (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K) (hP : ∀ i,(P i).IsHomogeneous d)
    (p₀ : Space m d q f u J counts O)
    (hlift : ∀ b,2≤b → b≤2*d →
      TargetLift ((Submodule.span K (Set.range (fun i =>
        (enumerateForms (forms hd hO hJ U P hP p₀) i).val)))*Forms K (h+m) d) d b) :
    ∃ D : MvPolynomial (Fin (finrank K (Space m d q f u J counts O))) K,
      eval ((Module.finBasis K _).equivFun p₀) D≠0 ∧
      ∀ a,eval a D≠0 → Function.Surjective (upperTargetMap
        (enumerateForms (forms hd hO hJ U P hP ((Module.finBasis K _).equivFun.symm a)))) := by
  have hwit := upperTargetMap_surjective_of_lifts
    (enumerateForms (forms hd hO hJ U P hP p₀)) hd hlift
  apply upperTarget_principal_open
    (fun a => enumerateForms (forms hd hO hJ U P hP ((Module.finBasis K _).equivFun.symm a)))
    (enumerated_forms_polynomial hd hO hJ U P hP) ((Module.finBasis K _).equivFun p₀)
  simpa only [LinearEquiv.symm_apply_apply] using hwit

theorem upper_target_open_linear_parameters {V : Type*}
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (L : V →ₗ[K] Space m d q f u J counts O) (hd : 0<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (U : Fin u → Forms K h d)
    (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K) (hP : ∀ i,(P i).IsHomogeneous d)
    (v₀ : V)
    (hlift : ∀ b,2≤b → b≤2*d →
      TargetLift ((Submodule.span K (Set.range (fun i =>
        (enumerateForms (forms hd hO hJ U P hP (L v₀)) i).val)))*Forms K (h+m) d) d b) :
    ∃ D : MvPolynomial (Fin (finrank K V)) K,
      eval ((Module.finBasis K V).equivFun v₀) D≠0 ∧
      ∀ a,eval a D≠0 → Function.Surjective (upperTargetMap
        (enumerateForms (forms hd hO hJ U P hP (L ((Module.finBasis K V).equivFun.symm a))))) := by
  have hwit := upperTargetMap_surjective_of_lifts
    (enumerateForms (forms hd hO hJ U P hP (L v₀))) hd hlift
  apply upperTarget_principal_open
    (fun a => enumerateForms (forms hd hO hJ U P hP (L ((Module.finBasis K V).equivFun.symm a))))
    (enumerated_forms_polynomial_linear_parameters L hd hO hJ U P hP)
    ((Module.finBasis K V).equivFun v₀)
  simpa only [LinearEquiv.symm_apply_apply] using hwit

end Froberg.PreparedTarget
