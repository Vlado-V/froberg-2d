module

public import Froberg.SplitTargetDual

@[expose] public section

/-! A projection vanishing on the bottom summand factors through the
higher summand, including on every value of a bilinear action. -/
noncomputable section
namespace Froberg
variable {K W W₀ H Z P V : Type} [Field K]
  [AddCommGroup W] [Module K W] [AddCommGroup W₀] [Module K W₀]
  [AddCommGroup H] [Module K H] [AddCommGroup Z] [Module K Z]
  [AddCommGroup P] [Module K P] [AddCommGroup V] [Module K V]

def splitHigherProjection (e : W ≃ₗ[K] W₀ × H) (f : W →ₗ[K] Z) : H →ₗ[K] Z :=
  f.comp (e.symm.toLinearMap.comp (LinearMap.inr K W₀ H))

theorem splitHigherProjection_factor (e : W ≃ₗ[K] W₀ × H) (f : W →ₗ[K] Z)
    (hf : ∀ x : W₀,f (e.symm (x,0))=0) (w : W) :
    splitHigherProjection e f (e w).2=f w := by
  have he : w=e.symm ((e w).1,0)+e.symm (0,(e w).2) := by
    rw [←map_add]
    simp only [Prod.mk_add_mk,add_zero,zero_add,Prod.eta,LinearEquiv.symm_apply_apply]
  calc
    _ = f (e.symm ((e w).1,0))+f (e.symm (0,(e w).2)) := by rw [hf,zero_add];rfl
    _ = f w := by rw [←map_add,←he]

theorem splitHigherProjection_action (e : W ≃ₗ[K] W₀ × H) (f : W →ₗ[K] Z)
    (hf : ∀ x : W₀,f (e.symm (x,0))=0)
    (mu : P →ₗ[K] V →ₗ[K] W) (p : P) (v : V) :
    splitHigherProjection e f (splitTargetHigherAction e mu p v)=f (mu p v) :=
  splitHigherProjection_factor e f hf (mu p v)

end Froberg
