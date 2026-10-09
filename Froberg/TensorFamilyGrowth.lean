module

public import Froberg.TensorFamilyQuotient
public import Froberg.TensorScalarGrowth
public import Froberg.AdditionalScalarGrowth

@[expose] public section

/-! Transport of the actual scalar-growth bound through family identities,
without expanding dependent quotient casts in downstream proofs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg
attribute [local instance] tensorQuotientGroup
open Module TensorProduct Quartic
variable {K U V W P : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [AddCommGroup P] [Module K P]

theorem scalarModulo_growth_of_eq (f g : U →ₗ[K] W) (hfg : f=g)
    (mu : P →ₗ[K] V →ₗ[K] W) (c : ℕ)
    (hf : ∀ L : Submodule K V,c*finrank K L≤
      finrank K (BilinearImage.image (scalarModulo f mu) L)) :
    ∀ L : Submodule K V,c*finrank K L≤
      finrank K (BilinearImage.image (scalarModulo g mu) L) := by
  subst g
  exact hf

variable {X Y Z A I : Type*}
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z] [AddCommGroup A] [Module K A] [Fintype I]

theorem tensorFamily_scalar_growth (F : X →ₗ[K] Z) (hF : Function.Surjective F)
    (f : A →ₗ[K] X ⊗[K] Y) (Q : I → Y) (c : ℕ)
    (hg : ∀ L : Submodule K Z,c*finrank K L≤finrank K (BilinearImage.image
      (scalarModulo (K := K) (U := A × (I → Z)) (V := Z) (P := Y) (W := Z ⊗[K] Y)
        (projectedTensorFamily F f Q) (tensorScalarProduct (K := K) (V := Z) (P := Y))) L))
    (L : Submodule K Z) :
    c*finrank K L≤finrank K (BilinearImage.image (tensorFamilyScalarAction F hF f Q) L) := by
  rw [tensorFamilyScalarAction_finrank]
  have heq : scalarModulo (K := K) (U := A × (I → Z)) (V := Z) (P := Y) (W := Z ⊗[K] Y)
      (projectedTensorFamily F f Q) (tensorScalarProduct (K := K) (V := Z) (P := Y))=
      projectedTensorScalarAction F f Q := by
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    rfl
  exact (hg L).trans_eq (congrArg
    (fun mu : Y →ₗ[K] Z →ₗ[K] ((Z ⊗[K] Y) ⧸ (projectedTensorFamily F f Q).range) =>
      finrank K (BilinearImage.image mu L)) heq)

end Froberg
