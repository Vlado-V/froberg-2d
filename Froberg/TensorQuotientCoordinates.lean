import Froberg.ProjectedQuotientEquiv

/-! Actual tensor quotient coordinates after a surjective projection of
the first factor. The additional relation space is arbitrary. -/
noncomputable section
namespace Froberg
open Module TensorProduct Quartic.SplitTensor
variable {K X Y Z : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]

local instance tensorQuotientGroup : AddCommGroup (X ⊗[K] Y) :=
  Module.addCommMonoidToAddCommGroup K

theorem tensorProjection_map_right (P : X →ₗ[K] Z) (hP : Function.Surjective P)
    (Q : Submodule K Y) :
    (rightRelations (X := X) Q).map (TensorProduct.map P (LinearMap.id : Y →ₗ[K] Y))=
      rightRelations (X := Z) Q := by
  rw [rightRelations,←LinearMap.range_comp]
  have he : (TensorProduct.map P (LinearMap.id : Y →ₗ[K] Y)).comp
      (TensorProduct.map (LinearMap.id : X →ₗ[K] X) Q.subtype)=
      (TensorProduct.map (LinearMap.id : Z →ₗ[K] Z) Q.subtype).comp
        (TensorProduct.map P (LinearMap.id : Q →ₗ[K] Q)) := by
    ext x y
    rfl
  rw [he,LinearMap.range_comp,LinearMap.range_eq_top.mpr
    (TensorProduct.map_surjective (g := P) (g' := LinearMap.id) hP Function.surjective_id)]
  exact Submodule.map_top _

theorem tensorProjection_relations_comap (P : X →ₗ[K] Z) (hP : Function.Surjective P)
    (Q : Submodule K Y) (E : Submodule K (X ⊗[K] Y)) :
    (rightRelations (X := Z) Q ⊔ E.map (TensorProduct.map P (LinearMap.id : Y →ₗ[K] Y))).comap
      (TensorProduct.map P (LinearMap.id : Y →ₗ[K] Y))=
      leftRelations P.ker ⊔ (rightRelations (X := X) Q ⊔ E) := by
  rw [←tensorProjection_map_right P hP Q,←Submodule.map_sup,Submodule.comap_map_eq,
    tensorProjection_kernel P hP]
  exact sup_comm _ _

def tensorQuotientMap (P : X →ₗ[K] Z) (hP : Function.Surjective P)
    (Q : Submodule K Y) (E : Submodule K (X ⊗[K] Y)) :
    ((X ⊗[K] Y) ⧸ (leftRelations P.ker ⊔ (rightRelations Q ⊔ E))) →ₗ[K]
      ((Z ⊗[K] Y) ⧸ (rightRelations Q ⊔ E.map (TensorProduct.map P (LinearMap.id : Y →ₗ[K] Y)))) :=
  (leftRelations P.ker ⊔ (rightRelations Q ⊔ E)).mapQ _
    (TensorProduct.map P (LinearMap.id : Y →ₗ[K] Y))
    (tensorProjection_relations_comap P hP Q E).ge

theorem tensorQuotientMap_bijective (P : X →ₗ[K] Z) (hP : Function.Surjective P)
    (Q : Submodule K Y) (E : Submodule K (X ⊗[K] Y)) :
    Function.Bijective (tensorQuotientMap P hP Q E) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [tensorQuotientMap,Submodule.ker_mapQ,tensorProjection_relations_comap P hP]
    exact Submodule.mkQ_map_self _
  · intro y
    obtain ⟨z,rfl⟩ := (rightRelations Q ⊔ E.map
      (TensorProduct.map P (LinearMap.id : Y →ₗ[K] Y))).mkQ_surjective y
    obtain ⟨x,rfl⟩ := TensorProduct.map_surjective (g := P) (g' := LinearMap.id)
      hP Function.surjective_id z
    exact ⟨(leftRelations P.ker ⊔ (rightRelations Q ⊔ E)).mkQ x,rfl⟩

def tensorQuotientEquiv (P : X →ₗ[K] Z) (hP : Function.Surjective P)
    (Q : Submodule K Y) (E : Submodule K (X ⊗[K] Y)) :
    ((X ⊗[K] Y) ⧸ (leftRelations P.ker ⊔ (rightRelations Q ⊔ E))) ≃ₗ[K]
      ((Z ⊗[K] Y) ⧸ (rightRelations Q ⊔ E.map (TensorProduct.map P (LinearMap.id : Y →ₗ[K] Y)))) :=
  LinearEquiv.ofBijective (tensorQuotientMap P hP Q E) (tensorQuotientMap_bijective P hP Q E)

@[simp] theorem tensorQuotientEquiv_tmul (P : X →ₗ[K] Z) (hP : Function.Surjective P)
    (Q : Submodule K Y) (E : Submodule K (X ⊗[K] Y)) (x : X) (y : Y) :
    tensorQuotientEquiv P hP Q E ((leftRelations P.ker ⊔ (rightRelations Q ⊔ E)).mkQ (x ⊗ₜ[K] y))=
      (rightRelations Q ⊔ E.map (TensorProduct.map P (LinearMap.id : Y →ₗ[K] Y))).mkQ (P x ⊗ₜ[K] y) := rfl

end Froberg
