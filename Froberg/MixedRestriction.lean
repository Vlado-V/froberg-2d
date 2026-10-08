import Froberg.UniversalMixedPosition

/-! Generic vector conditions are inherited by every injectively indexed
subfamily. -/
noncomputable section
namespace Froberg.MixedExterior
open Finset
variable {K α β : Type*} [Field K] [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β] {h : ℕ}

lemma full_spark_comp (v : β → Fin h → K)
    (hv : ∀ S : Finset β, S.card ≤ h → LinearIndependent K (fun i : S => v i.val))
    (e : α ↪ β) :
    ∀ S : Finset α, S.card ≤ h → LinearIndependent K (fun i : S => v (e i.val)) := by
  intro S hS
  let f : S → S.image e := fun i => ⟨e i.val, mem_image.mpr ⟨i.val,i.property,rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j he
    exact Subtype.ext (e.injective (congrArg Subtype.val he))
  exact (hv (S.image e) (by simpa only [card_image_of_injective _ e.injective] using hS)).comp f hf

lemma UniversalMixedPosition.comp {v : β → Fin h → K}
    (hv : UniversalMixedPosition v) (e : α ↪ β) :
    UniversalMixedPosition (fun i => v (e i)) := by
  intro c
  exact hv ⟨c.1,c.2.1,c.2.2.trans e⟩

end Froberg.MixedExterior
