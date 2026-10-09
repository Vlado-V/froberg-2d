module

public import Froberg.ScalarQuotientSlices
public import Quartic.QuotientBilinearImage
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section

/-! Taking a source-relation quotient and then scalar-family relations is
exactly quotienting the original target by the sum of both relation spaces. -/
noncomputable section
namespace Froberg.BilinearScalarFamily
open Module Quartic
variable {K P V W : Type*} [Field K]
  [AddCommGroup P] [Module K P] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] {q : ℕ}

theorem quotientScalarFamily_mk (mu : P →ₗ[K] V →ₗ[K] W)
    (E : Submodule K V) (Q : Fin q → P) (v : Fin q → V) :
    multiplication (QuotientBilinearImage.quotientMap mu E) Q (fun i => E.mkQ (v i))=
      (BilinearImage.image mu E).mkQ (multiplication mu Q v) := by
  simp [multiplication,tupleBilinear,BilinearImage.tupleMap,
    QuotientBilinearImage.quotientMap]

theorem quotientScalarFamily_range (mu : P →ₗ[K] V →ₗ[K] W)
    (E : Submodule K V) (Q : Fin q → P) :
    (multiplication (QuotientBilinearImage.quotientMap mu E) Q).range=
      (multiplication mu Q).range.map (BilinearImage.image mu E).mkQ := by
  ext z
  constructor
  · rintro ⟨v,rfl⟩
    choose w hw using fun i => E.mkQ_surjective (v i)
    have hv : v=fun i => E.mkQ (w i) := funext (fun i => (hw i).symm)
    rw [hv,quotientScalarFamily_mk]
    exact ⟨_,⟨w,rfl⟩,rfl⟩
  · rintro ⟨_,⟨v,rfl⟩,rfl⟩
    exact ⟨_,quotientScalarFamily_mk mu E Q v⟩

def scalarDoubleQuotientEquiv (mu : P →ₗ[K] V →ₗ[K] W)
    (E : Submodule K V) (Q : Fin q → P) :
    ((W ⧸ BilinearImage.image mu E) ⧸
      (multiplication (QuotientBilinearImage.quotientMap mu E) Q).range) ≃ₗ[K]
      (W ⧸ (BilinearImage.image mu E ⊔ (multiplication mu Q).range)) :=
  (Submodule.quotEquivOfEq _ _ (quotientScalarFamily_range mu E Q)).trans
    (Submodule.quotientQuotientEquivQuotientSup _ _)

@[simp] theorem scalarDoubleQuotientEquiv_mk (mu : P →ₗ[K] V →ₗ[K] W)
    (E : Submodule K V) (Q : Fin q → P) (w : W) :
    scalarDoubleQuotientEquiv mu E Q
      ((multiplication (QuotientBilinearImage.quotientMap mu E) Q).range.mkQ
        ((BilinearImage.image mu E).mkQ w))=
      (BilinearImage.image mu E ⊔ (multiplication mu Q).range).mkQ w := rfl

end Froberg.BilinearScalarFamily
