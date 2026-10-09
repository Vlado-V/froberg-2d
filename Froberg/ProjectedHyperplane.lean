module

public import Froberg.FormalHyperplane
public import Froberg.ProjectedHomologyCoefficients

@[expose] public section

/-! Exact replacement and retained old homology for the actual endpoint
complex after deleting a fixed target subspace. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module
variable {K : Type} [Field K]
variable {Z : Type*} [AddCommGroup Z] [Module K Z]
variable {n d r : ℕ}

def projectedHyperplaneReplacement (pi : Forms K n (2*d) →ₗ[K] Z)
    (W A Q Qminus W₀ : Submodule K (Forms K n d))
    {f M : Forms K n d} {e : K}
    (hWA : W ⊓ A=Q) (hQ : Q=Qminus ⊔ Submodule.span K {f})
    (hW : W=W₀ ⊔ Submodule.span K {f}) (hQ₀ : Qminus ≤ W₀)
    (hf₀ : f ∉ W₀) (hM : M ∉ W ⊔ A) (he : e ≠ 0)
    (hrelations : (pi.comp formalPolynomialMultiplication).ker ⊓
      formalMixed (W ⊔ Submodule.span K {M})=
      (pi.comp formalPolynomialMultiplication).ker ⊓ formalProducts Q A)
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (hspan : Submodule.span K (Set.range q)=W₀ ⊔ Submodule.span K {f+e • M}) :
    ProjectedEndpointHomology pi q ≃ₗ[K]
      ((pi.comp formalPolynomialMultiplication).ker ⊓ formalProducts Qminus A :
        Submodule K (SymmetricSquare K (Forms K n d))) := by
  have hEq : (pi.comp formalPolynomialMultiplication).ker ⊓
      formalMixed (Submodule.span K (Set.range q))=
      (pi.comp formalPolynomialMultiplication).ker ⊓ formalProducts Qminus A := by
    rw [hspan]
    exact formal_hyperplane_replacement _ W A Q Qminus W₀ hWA hQ hW hQ₀ hf₀ hM he hrelations
  exact (projectedHomologyEquivFormal pi q hq).trans (LinearEquiv.ofEq _ _ hEq)

def projectedRetainedHomologyEquivFormal (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (W : Submodule K (Forms K n d)) (hW : W ≤ Submodule.span K (Set.range q)) :
    projectedRetainedHomology pi q hq W ≃ₗ[K]
      ((pi.comp formalPolynomialMultiplication).ker ⊓ formalMixed W :
        Submodule K (SymmetricSquare K (Forms K n d))) := by
  let L : projectedRetainedHomology pi q hq W →ₗ[K]
      ((pi.comp formalPolynomialMultiplication).ker ⊓ formalMixed W :
        Submodule K (SymmetricSquare K (Forms K n d))) :=
    { toFun := fun x => ⟨projectedFormalRepresentative pi q hq x.val,
        (projectedFormalRepresentative_mem pi q hq x.val).1,x.property⟩
      map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
  apply LinearEquiv.ofBijective L
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply projectedFormalRepresentative_injective pi q hq
    change (L x).val=(L y).val
    exact congrArg Subtype.val hxy
  · intro x
    let e := projectedHomologyEquivFormal pi q hq
    let x' : ((pi.comp formalPolynomialMultiplication).ker ⊓
        formalMixed (Submodule.span K (Set.range q)) :
          Submodule K (SymmetricSquare K (Forms K n d))) :=
      ⟨x.val,x.property.1,formalMixed_mono hW x.property.2⟩
    have hrep : projectedFormalRepresentative pi q hq (e.symm x')=x.val :=
      congrArg Subtype.val (e.apply_symm_apply x')
    refine ⟨⟨e.symm x',?_⟩,?_⟩
    · change projectedFormalRepresentative pi q hq (e.symm x') ∈ formalMixed W
      rw [hrep]
      exact x.property.2
    · apply Subtype.ext
      exact hrep

theorem projectedRetainedHomology_finrank (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (W : Submodule K (Forms K n d)) (hW : W ≤ Submodule.span K (Set.range q)) :
    finrank K (projectedRetainedHomology pi q hq W)=
      finrank K ((pi.comp formalPolynomialMultiplication).ker ⊓ formalMixed W :
        Submodule K (SymmetricSquare K (Forms K n d))) :=
  (projectedRetainedHomologyEquivFormal pi q hq W hW).finrank_eq

end Froberg
