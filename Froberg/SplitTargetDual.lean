import Froberg.BilinearPostcompose

/-! A target decomposition gives the actual dual restriction and
reconstruction maps used in the layered covector argument. -/
noncomputable section
namespace Froberg
variable {K W W₀ H P V : Type} [Field K]
  [AddCommGroup W] [Module K W] [AddCommGroup W₀] [Module K W₀]
  [AddCommGroup H] [Module K H] [AddCommGroup P] [Module K P]
  [AddCommGroup V] [Module K V]

def splitTargetBottom (e : W ≃ₗ[K] W₀ × H) :
    (W →ₗ[K] K) →ₗ[K] (W₀ →ₗ[K] K) :=
  (e.symm.toLinearMap.comp (LinearMap.inl K W₀ H)).dualMap

def splitTargetHigher (e : W ≃ₗ[K] W₀ × H) :
    (W →ₗ[K] K) →ₗ[K] (H →ₗ[K] K) :=
  (e.symm.toLinearMap.comp (LinearMap.inr K W₀ H)).dualMap

def splitTargetReconstruct (e : W ≃ₗ[K] W₀ × H) :
    ((W₀ →ₗ[K] K) × (H →ₗ[K] K)) →ₗ[K] (W →ₗ[K] K) :=
  e.toLinearMap.dualMap.comp
    ((LinearMap.fst K W₀ H).dualMap.coprod (LinearMap.snd K W₀ H).dualMap)

theorem splitTarget_evaluation (e : W ≃ₗ[K] W₀ × H) (ell : W →ₗ[K] K) (w : W) :
    ell w=splitTargetBottom e ell (e w).1+splitTargetHigher e ell (e w).2 := by
  change ell w=ell (e.symm ((e w).1,0))+ell (e.symm (0,(e w).2))
  rw [←map_add,←map_add]
  simp only [Prod.mk_add_mk,add_zero,zero_add,Prod.eta,LinearEquiv.symm_apply_apply]

theorem splitTarget_reconstruct (e : W ≃ₗ[K] W₀ × H) (ell : W →ₗ[K] K) :
    splitTargetReconstruct e (splitTargetBottom e ell,splitTargetHigher e ell)=ell := by
  apply LinearMap.ext
  intro w
  exact (splitTarget_evaluation e ell w).symm

def splitTargetBottomAction (e : W ≃ₗ[K] W₀ × H) (mu : P →ₗ[K] V →ₗ[K] W) :
    P →ₗ[K] V →ₗ[K] W₀ :=
  mu.compr₂ₛₗ ((LinearMap.fst K W₀ H).comp e.toLinearMap)

def splitTargetHigherAction (e : W ≃ₗ[K] W₀ × H) (mu : P →ₗ[K] V →ₗ[K] W) :
    P →ₗ[K] V →ₗ[K] H :=
  mu.compr₂ₛₗ ((LinearMap.snd K W₀ H).comp e.toLinearMap)

theorem splitTarget_action_compat (e : W ≃ₗ[K] W₀ × H)
    (mu : P →ₗ[K] V →ₗ[K] W) (ell : W →ₗ[K] K) (p : P) (v : V) :
    ell (mu p v)=splitTargetBottom e ell (splitTargetBottomAction e mu p v)+
      splitTargetHigher e ell (splitTargetHigherAction e mu p v) :=
  splitTarget_evaluation e ell (mu p v)

end Froberg
