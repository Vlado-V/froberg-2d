import Froberg.MixedQuotientExactness
import Quartic.SplitTensor

/-! The actual tensor-product exact sequence behind the odd top quotient.
The left term is U tensor (Y/Q), not a dimensionally substituted vector space. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module TensorProduct Quartic.SplitTensor
variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- The actual quotient map on the left relation tensors. -/
def mixedTensorMap (U : Submodule K X) (Q : Submodule K Y)
    (E : Submodule K (X ⊗[K] Y)) :
    (U ⊗[K] Y) →ₗ[K] (X ⊗[K] Y) ⧸ (rightRelations Q ⊔ E) :=
  (rightRelations Q ⊔ E).mkQ.comp (TensorProduct.map U.subtype LinearMap.id)

theorem mixedTensorMap_kernel (U : Submodule K X) (Q : Submodule K Y)
    (E : Submodule K (X ⊗[K] Y)) (hE : Disjoint E (leftRelations U ⊔ rightRelations Q)) :
    (mixedTensorMap U Q E).ker=(TensorProduct.map (LinearMap.id : U →ₗ[K] U) Q.mkQ).ker := by
  have hcomm : TensorProduct.map (LinearMap.id : X →ₗ[K] X) Q.mkQ ∘ₗ
      TensorProduct.map U.subtype (LinearMap.id : Y →ₗ[K] Y) =
      TensorProduct.map U.subtype (LinearMap.id : (Y ⧸ Q) →ₗ[K] (Y ⧸ Q)) ∘ₗ
        TensorProduct.map (LinearMap.id : U →ₗ[K] U) Q.mkQ := by
    ext u y
    simp
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := Y ⧸ Q)
    U.subtype U.subtype_injective
  have hk : (TensorProduct.map (LinearMap.id : X →ₗ[K] X) Q.mkQ).ker =
      rightRelations Q := lTensor_mkQ X Q
  ext v
  change TensorProduct.map U.subtype LinearMap.id v ∈ (rightRelations Q ⊔ E).mkQ.ker ↔ _
  rw [Submodule.ker_mkQ]
  constructor
  · intro hv
    have hleft : TensorProduct.map U.subtype LinearMap.id v ∈ leftRelations U := ⟨v,rfl⟩
    have hboth : TensorProduct.map U.subtype LinearMap.id v ∈ leftRelations U ⊓ (rightRelations Q ⊔ E) :=
      ⟨hleft,hv⟩
    rw [mixed_intersection_of_disjoint _ _ _ hE] at hboth
    have hz : TensorProduct.map (LinearMap.id : X →ₗ[K] X) Q.mkQ
        (TensorProduct.map U.subtype LinearMap.id v)=0 := by
      exact (show rightRelations Q ≤ _ from hk.ge) hboth.2
    change TensorProduct.map (LinearMap.id : U →ₗ[K] U) Q.mkQ v=0
    apply hinj
    rw [map_zero]
    exact (congrArg (fun F : U ⊗[K] Y →ₗ[K] X ⊗[K] (Y ⧸ Q) => F v) hcomm).symm.trans hz
  · intro hv
    have hz : TensorProduct.map (LinearMap.id : X →ₗ[K] X) Q.mkQ
        (TensorProduct.map U.subtype LinearMap.id v)=0 := by
      have he := congrArg (fun F : U ⊗[K] Y →ₗ[K] X ⊗[K] (Y ⧸ Q) => F v) hcomm
      change TensorProduct.map (LinearMap.id : U →ₗ[K] U) Q.mkQ v=0 at hv
      simpa only [LinearMap.comp_apply,hv,map_zero] using he
    exact (show rightRelations Q ≤ rightRelations Q ⊔ E from le_sup_left)
      ((show _ ≤ rightRelations Q from hk.le) hz)

/-- The canonical left injection in C.10. -/
def mixedTensorInjection (U : Submodule K X) (Q : Submodule K Y)
    (E : Submodule K (X ⊗[K] Y)) (hE : Disjoint E (leftRelations U ⊔ rightRelations Q)) :
    (U ⊗[K] (Y ⧸ Q)) →ₗ[K] (X ⊗[K] Y) ⧸ (rightRelations Q ⊔ E) :=
  (TensorProduct.map (LinearMap.id : U →ₗ[K] U) Q.mkQ).liftOfSurjective
    (TensorProduct.map_surjective (g := (LinearMap.id : U →ₗ[K] U))
      (g' := Q.mkQ) Function.surjective_id Q.mkQ_surjective)
    ⟨mixedTensorMap U Q E,(mixedTensorMap_kernel U Q E hE).ge⟩

@[simp] theorem mixedTensorInjection_map (U : Submodule K X) (Q : Submodule K Y)
    (E : Submodule K (X ⊗[K] Y)) (hE : Disjoint E (leftRelations U ⊔ rightRelations Q))
    (v : U ⊗[K] Y) :
    mixedTensorInjection U Q E hE (TensorProduct.map (LinearMap.id : U →ₗ[K] U) Q.mkQ v)=
      mixedTensorMap U Q E v := by
  exact LinearMap.equivOfSurjective_apply _ _

@[simp] theorem mixedTensorInjection_tmul (U : Submodule K X) (Q : Submodule K Y)
    (E : Submodule K (X ⊗[K] Y)) (hE : Disjoint E (leftRelations U ⊔ rightRelations Q))
    (u : U) (y : Y) :
    mixedTensorInjection U Q E hE (u ⊗ₜ[K] Q.mkQ y)=
      (rightRelations Q ⊔ E).mkQ (u.val ⊗ₜ[K] y) := by
  simpa only [TensorProduct.map_tmul,LinearMap.id_apply,mixedTensorMap,
    LinearMap.comp_apply,Submodule.subtype_apply] using mixedTensorInjection_map U Q E hE (u ⊗ₜ[K] y)

theorem mixedTensorInjection_injective (U : Submodule K X) (Q : Submodule K Y)
    (E : Submodule K (X ⊗[K] Y)) (hE : Disjoint E (leftRelations U ⊔ rightRelations Q)) :
    Function.Injective (mixedTensorInjection U Q E hE) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  obtain ⟨w,rfl⟩ := TensorProduct.map_surjective (g := (LinearMap.id : U →ₗ[K] U))
      (g' := Q.mkQ) Function.surjective_id Q.mkQ_surjective v
  rw [mixedTensorInjection_map] at hv
  exact (show (mixedTensorMap U Q E).ker ≤ _ from (mixedTensorMap_kernel U Q E hE).le) hv

theorem mixedTensorInjection_range (U : Submodule K X) (Q : Submodule K Y)
    (E : Submodule K (X ⊗[K] Y)) (hE : Disjoint E (leftRelations U ⊔ rightRelations Q)) :
    (mixedTensorInjection U Q E hE).range=(leftRelations U).map (rightRelations Q ⊔ E).mkQ := by
  ext v
  constructor
  · rintro ⟨w,rfl⟩
    obtain ⟨z,rfl⟩ := TensorProduct.map_surjective (g := (LinearMap.id : U →ₗ[K] U))
      (g' := Q.mkQ) Function.surjective_id Q.mkQ_surjective w
    rw [mixedTensorInjection_map]
    exact ⟨TensorProduct.map U.subtype LinearMap.id z,⟨z,rfl⟩,rfl⟩
  · rintro ⟨w,⟨z,rfl⟩,rfl⟩
    exact ⟨TensorProduct.map (LinearMap.id : U →ₗ[K] U) Q.mkQ z,mixedTensorInjection_map U Q E hE z⟩

theorem mixedTensor_exact (U : Submodule K X) (Q : Submodule K Y)
    (E : Submodule K (X ⊗[K] Y)) (hE : Disjoint E (leftRelations U ⊔ rightRelations Q)) :
    (mixedTensorInjection U Q E hE).range=
      (mixedQuotientProjection (leftRelations U) (rightRelations Q) E).ker := by
  rw [mixedTensorInjection_range,mixedQuotientProjection_kernel]

theorem mixedTensor_finrank [FiniteDimensional K X] [FiniteDimensional K Y]
    (U : Submodule K X) (Q : Submodule K Y)
    (E : Submodule K (X ⊗[K] Y)) (hE : Disjoint E (leftRelations U ⊔ rightRelations Q)) :
    finrank K ((X ⊗[K] Y) ⧸ (rightRelations Q ⊔ E)) =
      finrank K (U ⊗[K] (Y ⧸ Q)) +
        finrank K ((X ⊗[K] Y) ⧸ ((leftRelations U ⊔ rightRelations Q) ⊔ E)) := by
  have hd := (mixedQuotientProjection (leftRelations U) (rightRelations Q) E).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (mixedQuotientProjection_surjective _ _ _),finrank_top,
    ← mixedTensor_exact U Q E hE,
    LinearMap.finrank_range_of_inj (mixedTensorInjection_injective U Q E hE)] at hd
  omega

end Froberg
