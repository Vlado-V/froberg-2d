module

public import Froberg.PreparedUpperTargetOpen
public import Froberg.PreparedPrivateComponents
public import Froberg.PreparedTargetRestrictions

@[expose] public section

/-! Enumeration preserves the actual generated product space. This turns
the literal prepared-family witness into a polynomial rank-open certificate. -/
noncomputable section
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

 theorem enumerateForms_range
    (g : Label q f u J counts → homogeneousSubmodule (Fin h ⊕ Fin m) K d) :
    Set.range (fun i => (enumerateForms g i).val)=
      Set.range (fun i => rename finSumFinEquiv (g i).val) := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨(Fintype.equivFin _).symm i,rfl⟩
  · rintro ⟨i,rfl⟩
    refine ⟨Fintype.equivFin _ i,?_⟩
    simp only [enumerateForms,LinearMap.coe_mk,AddHom.coe_mk,Equiv.symm_apply_apply]

theorem enumerate_forms_productSpace (hd : 0<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (U : Fin u → Forms K h d)
    (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K) (hP : ∀ i,(P i).IsHomogeneous d)
    (p : Space m d q f u J counts O) :
    (Submodule.span K (Set.range (fun i => (enumerateForms (forms hd hO hJ U P hP p) i).val)))*Forms K (h+m) d=
      (Submodule.span K (Set.range (renamedGenerator U P p)))*Forms K (h+m) d := by
  rw [enumerateForms_range]
  rfl

theorem upper_target_open_of_literal_witness (hd : 0<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    [Module.Finite K (Space m d q f u J counts O)]
    (U : Fin u → Forms K h d)
    (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K) (hP : ∀ i,(P i).IsHomogeneous d)
    (p₀ : Space m d q f u J counts O)
    (hlift : ∀ b,2≤b → b≤2*d → TargetLift
      ((Submodule.span K (Set.range (renamedGenerator U P p₀)))*Forms K (h+m) d) d b) :
    ∃ D : MvPolynomial (Fin (finrank K (Space m d q f u J counts O))) K,
      eval ((Module.finBasis K _).equivFun p₀) D≠0 ∧
      ∀ a,eval a D≠0 → Function.Surjective (upperTargetMap
        (enumerateForms (forms hd hO hJ U P hP ((Module.finBasis K _).equivFun.symm a)))) := by
  apply upper_target_open_of_witness hd hO hJ U P hP p₀
  simpa only [enumerate_forms_productSpace] using hlift

theorem upper_target_open_linear_of_literal_witness {V : Type*}
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (L : V →ₗ[K] Space m d q f u J counts O) (hd : 0<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (U : Fin u → Forms K h d)
    (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K) (hP : ∀ i,(P i).IsHomogeneous d)
    (v₀ : V)
    (hlift : ∀ b,2≤b → b≤2*d → TargetLift
      ((Submodule.span K (Set.range (renamedGenerator U P (L v₀))))*Forms K (h+m) d) d b) :
    ∃ D : MvPolynomial (Fin (finrank K V)) K,
      eval ((Module.finBasis K V).equivFun v₀) D≠0 ∧
      ∀ a,eval a D≠0 → Function.Surjective (upperTargetMap
        (enumerateForms (forms hd hO hJ U P hP (L ((Module.finBasis K V).equivFun.symm a))))) := by
  apply upper_target_open_linear_parameters L hd hO hJ U P hP v₀
  simpa only [enumerate_forms_productSpace] using hlift

end Froberg.PreparedTarget
