module

public import Froberg.ProjectedRelationSeparation

@[expose] public section

/-! Canonical identification of a quotient after a surjective target
projection with the quotient by its kernel and the original relations. -/
noncomputable section
namespace Froberg
open Module TensorProduct Quartic.SplitTensor
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def projectedQuotientMap (P : V →ₗ[K] W) (A : Submodule K V) :
    (V ⧸ (P.ker ⊔ A)) →ₗ[K] W ⧸ A.map P :=
  (P.ker ⊔ A).mapQ (A.map P) P (by
    rw [Submodule.comap_map_eq,sup_comm A P.ker])

theorem projectedQuotientMap_bijective (P : V →ₗ[K] W) (hP : Function.Surjective P)
    (A : Submodule K V) : Function.Bijective (projectedQuotientMap P A) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [projectedQuotientMap,Submodule.ker_mapQ,Submodule.comap_map_eq,sup_comm A P.ker]
    exact (P.ker ⊔ A).mkQ_map_self
  · intro y
    obtain ⟨w,rfl⟩ := (A.map P).mkQ_surjective y
    obtain ⟨v,rfl⟩ := hP w
    exact ⟨(P.ker ⊔ A).mkQ v,rfl⟩

def projectedQuotientEquiv (P : V →ₗ[K] W) (hP : Function.Surjective P)
    (A : Submodule K V) : (V ⧸ (P.ker ⊔ A)) ≃ₗ[K] W ⧸ A.map P :=
  LinearEquiv.ofBijective (projectedQuotientMap P A) (projectedQuotientMap_bijective P hP A)

@[simp] theorem projectedQuotientEquiv_mk (P : V →ₗ[K] W) (hP : Function.Surjective P)
    (A : Submodule K V) (x : V) :
    projectedQuotientEquiv P hP A ((P.ker ⊔ A).mkQ x)=(A.map P).mkQ (P x) := rfl

section Tensor
variable {X Y Z : Type*}
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]

theorem tensorProjection_kernel (P : X →ₗ[K] Z) (hP : Function.Surjective P) :
    (TensorProduct.map P (LinearMap.id : Y →ₗ[K] Y)).ker=leftRelations P.ker := by
  exact (rTensor_exact Y P.exact_subtype_ker_map hP).linearMap_ker_eq

end Tensor
end Froberg
