module

public import Froberg.PreparedTargetFamily

@[expose] public section

/-! The complete prepared family as a polynomially varying tuple of actual
homogeneous forms, with an explicit finite enumeration of its labels. -/
noncomputable section
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem variableGenerator_homogeneous (hd : 0<d)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) (hJ : ∀ j∈J,j≤d)
    (p : Space m d q f u J counts O) (i : Label q f u J counts) :
    (variableGenerator p i).IsHomogeneous d := by
  rcases i with i | (i | i)
  · exact PreparedParameters.generator_homogeneous hO hJ p.1 i
  · change (p.2.1 i).val∈homogeneousSubmodule (σ ⊕ Fin m) K d
    have hh := biformImage_homogeneous (homogeneousSubmodule σ K 1) (Forms K m (d-1))
      le_rfl le_rfl (p.2.1 i).property
    simpa only [show 1+(d-1)=d by omega] using hh
  · exact (p.2.2 i).property.rename_isHomogeneous

def variableForms (hd : 0<d)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) (hJ : ∀ j∈J,j≤d) :
    Space m d q f u J counts O →ₗ[K]
      (Label q f u J counts → homogeneousSubmodule (σ ⊕ Fin m) K d) where
  toFun p i := ⟨variableGenerator p i,variableGenerator_homogeneous hd hO hJ p i⟩
  map_add' p p' := by
    funext i
    apply Subtype.ext
    exact congrFun (map_add variableGenerator p p') i
  map_smul' a p := by
    funext i
    apply Subtype.ext
    exact congrFun (map_smul variableGenerator a p) i

def fixedForms (U : Fin u → homogeneousSubmodule σ K d)
    (P : Fin u → MvPolynomial (σ ⊕ Fin m) K) (hP : ∀ i,(P i).IsHomogeneous d) :
    Label q f u J counts → homogeneousSubmodule (σ ⊕ Fin m) K d :=
  fun i => ⟨fixedGenerator U P i,by
    rcases i with i | (i | i)
    · exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_zero _ _ _
    · exact (U i).property.rename_isHomogeneous.add (hP i)⟩

def forms (hd : 0<d)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) (hJ : ∀ j∈J,j≤d)
    (U : Fin u → homogeneousSubmodule σ K d)
    (P : Fin u → MvPolynomial (σ ⊕ Fin m) K) (hP : ∀ i,(P i).IsHomogeneous d)
    (p : Space m d q f u J counts O) :
    Label q f u J counts → homogeneousSubmodule (σ ⊕ Fin m) K d :=
  variableForms hd hO hJ p+fixedForms U P hP

@[simp] theorem forms_val (hd : 0<d)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) (hJ : ∀ j∈J,j≤d)
    (U : Fin u → homogeneousSubmodule σ K d)
    (P : Fin u → MvPolynomial (σ ⊕ Fin m) K) (hP : ∀ i,(P i).IsHomogeneous d)
    (p : Space m d q f u J counts O) (i : Label q f u J counts) :
    (forms hd hO hJ U P hP p i).val=generator U P p i := rfl

theorem forms_polynomial (hd : 0<d)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) (hJ : ∀ j∈J,j≤d)
    [Module.Finite K (Space m d q f u J counts O)]
    (U : Fin u → homogeneousSubmodule σ K d)
    (P : Fin u → MvPolynomial (σ ⊕ Fin m) K) (hP : ∀ i,(P i).IsHomogeneous d) :
    IsPolynomialFamily (fun a : Fin (finrank K (Space m d q f u J counts O)) → K =>
      forms hd hO hJ U P hP ((Module.finBasis K _).equivFun.symm a)) :=
  (isPolynomialFamily_linear ((variableForms hd hO hJ).comp
    (Module.finBasis K (Space m d q f u J counts O)).equivFun.symm.toLinearMap)).add
      (isPolynomialFamily_const (fixedForms U P hP))

theorem forms_polynomial_linear_parameters {V : Type*}
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (L : V →ₗ[K] Space m d q f u J counts O) (hd : 0<d)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) (hJ : ∀ j∈J,j≤d)
    (U : Fin u → homogeneousSubmodule σ K d)
    (P : Fin u → MvPolynomial (σ ⊕ Fin m) K) (hP : ∀ i,(P i).IsHomogeneous d) :
    IsPolynomialFamily (fun a : Fin (finrank K V) → K =>
      forms hd hO hJ U P hP (L ((Module.finBasis K V).equivFun.symm a))) :=
  (isPolynomialFamily_linear (((variableForms hd hO hJ).comp L).comp
    (Module.finBasis K V).equivFun.symm.toLinearMap)).add
      (isPolynomialFamily_const (fixedForms U P hP))

variable {h : ℕ}

def enumerateForms :
    (Label q f u J counts → homogeneousSubmodule (Fin h ⊕ Fin m) K d) →ₗ[K]
      (Fin (Fintype.card (Label q f u J counts)) → Forms K (h+m) d) where
  toFun g i := ⟨rename finSumFinEquiv (g ((Fintype.equivFin _).symm i)).val,
    (g ((Fintype.equivFin _).symm i)).property.rename_isHomogeneous⟩
  map_add' g g' := by funext i;apply Subtype.ext;exact map_add _ _ _
  map_smul' a g := by funext i;apply Subtype.ext;exact map_smul _ _ _

theorem enumerated_forms_polynomial (hd : 0<d)
    {O : ℕ → Submodule K (Poly K h)}
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    [Module.Finite K (Space m d q f u J counts O)]
    (U : Fin u → Forms K h d)
    (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K) (hP : ∀ i,(P i).IsHomogeneous d) :
    IsPolynomialFamily (fun a : Fin (finrank K (Space m d q f u J counts O)) → K =>
      enumerateForms (forms hd hO hJ U P hP ((Module.finBasis K _).equivFun.symm a))) :=
  (forms_polynomial hd hO hJ U P hP).linear_comp enumerateForms

theorem enumerated_forms_polynomial_linear_parameters {V : Type*}
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    {O : ℕ → Submodule K (Poly K h)}
    (L : V →ₗ[K] Space m d q f u J counts O) (hd : 0<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (U : Fin u → Forms K h d)
    (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K) (hP : ∀ i,(P i).IsHomogeneous d) :
    IsPolynomialFamily (fun a : Fin (finrank K V) → K =>
      enumerateForms (forms hd hO hJ U P hP (L ((Module.finBasis K V).equivFun.symm a)))) :=
  (forms_polynomial_linear_parameters L hd hO hJ U P hP).linear_comp enumerateForms

end Froberg.PreparedTarget
