import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-! The higher projection of a subspace has dimension equal to its total
dimension minus its intersection with the bottom coordinate space. -/
noncomputable section
namespace Froberg
open Module
variable {K X Y V : Type*} [Field K]
  [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem product_snd_finrank (L : Submodule K (X × Y)) :
    finrank K (L.map (LinearMap.snd K X Y))=
      finrank K L-finrank K (L.comap (LinearMap.inl K X Y)) := by
  let f := (LinearMap.snd K X Y).comp L.subtype
  let inc : L.comap (LinearMap.inl K X Y) →ₗ[K] L :=
    { toFun := fun x => ⟨(x.val,0),x.property⟩
      map_add' := fun x y => Subtype.ext (by ext <;> simp)
      map_smul' := fun c x => Subtype.ext (by ext <;> simp) }
  have hi : Function.Injective inc := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : L => z.val.1) hxy
  have hk : f.ker=inc.range := by
    ext w
    constructor
    · intro hw
      change w.val.2=0 at hw
      have hm : (w.val.1,0)∈L := by
        have he : (w.val.1,0)=w.val := Prod.ext rfl hw.symm
        rw [he]
        exact w.property
      exact ⟨⟨w.val.1,hm⟩,Subtype.ext (Prod.ext rfl hw.symm)⟩
    · rintro ⟨x,rfl⟩
      rfl
  have hr : f.range=L.map (LinearMap.snd K X Y) := by
    change ((LinearMap.snd K X Y).comp L.subtype).range=_
    rw [LinearMap.range_comp,Submodule.range_subtype]
  have h := f.finrank_range_add_finrank_ker
  rw [hr,hk,LinearMap.finrank_range_of_inj hi] at h
  omega

theorem coordinates_higher_finrank (e : V ≃ₗ[K] X × Y) (L : Submodule K V) :
    finrank K (L.map ((LinearMap.snd K X Y).comp e.toLinearMap))=
      finrank K L-finrank K (L.comap (e.symm.toLinearMap.comp (LinearMap.inl K X Y))) := by
  have hc : (L.map e.toLinearMap).comap (LinearMap.inl K X Y)=
      L.comap (e.symm.toLinearMap.comp (LinearMap.inl K X Y)) := by
    ext x
    constructor
    · rintro ⟨v,hv,he⟩
      change e.symm (x,0)∈L
      change e v=(x,0) at he
      rw [←he,e.symm_apply_apply]
      exact hv
    · intro hx
      exact ⟨e.symm (x,0),hx,e.apply_symm_apply _⟩
  rw [Submodule.map_comp,product_snd_finrank,hc,e.finrank_map_eq]

end Froberg
