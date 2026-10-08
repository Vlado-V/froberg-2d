import Froberg.SplitTargetDual
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Covectors on the full target restrict to the split ambient target.
Surjectivity supplies reconstruction on precisely those covectors, with
no assumption that arbitrary bottom covectors extend through the quotient. -/
noncomputable section
namespace Froberg
variable {K W A W₀ H P V : Type} [Field K]
  [AddCommGroup W] [Module K W] [AddCommGroup A] [Module K A]
  [AddCommGroup W₀] [Module K W₀] [AddCommGroup H] [Module K H]
  [AddCommGroup P] [Module K P] [AddCommGroup V] [Module K V]

def quotientSplitBottom (e : A ≃ₗ[K] W₀ × H) (pi : A →ₗ[K] W) :
    (W →ₗ[K] K) →ₗ[K] (W₀ →ₗ[K] K) :=
  (splitTargetBottom e).comp pi.dualMap

def quotientSplitHigher (e : A ≃ₗ[K] W₀ × H) (pi : A →ₗ[K] W) :
    (W →ₗ[K] K) →ₗ[K] (H →ₗ[K] K) :=
  (splitTargetHigher e).comp pi.dualMap

def quotientSplitReconstruct (e : A ≃ₗ[K] W₀ × H) (pi : A →ₗ[K] W) :
    ((W₀ →ₗ[K] K) × (H →ₗ[K] K)) →ₗ[K] (W →ₗ[K] K) :=
  pi.dualMap.leftInverse.comp (splitTargetReconstruct e)

theorem surjective_dual_ker (pi : A →ₗ[K] W) (hpi : Function.Surjective pi) :
    pi.dualMap.ker=⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  intro ell ell' h
  apply LinearMap.ext
  intro w
  obtain ⟨a,rfl⟩ := hpi w
  exact LinearMap.congr_fun h a

theorem quotientSplit_reconstruct (e : A ≃ₗ[K] W₀ × H)
    (pi : A →ₗ[K] W) (hpi : Function.Surjective pi) (ell : W →ₗ[K] K) :
    quotientSplitReconstruct e pi (quotientSplitBottom e pi ell,quotientSplitHigher e pi ell)=ell := by
  change pi.dualMap.leftInverse
    (splitTargetReconstruct e (splitTargetBottom e (pi.dualMap ell),
      splitTargetHigher e (pi.dualMap ell)))=ell
  rw [splitTarget_reconstruct]
  exact LinearMap.leftInverse_apply_of_inj (surjective_dual_ker pi hpi) ell

theorem quotientSplit_evaluation (e : A ≃ₗ[K] W₀ × H)
    (pi : A →ₗ[K] W) (ell : W →ₗ[K] K) (a : A) :
    ell (pi a)=quotientSplitBottom e pi ell (e a).1+
      quotientSplitHigher e pi ell (e a).2 :=
  splitTarget_evaluation e (pi.dualMap ell) a

theorem quotientSplit_action_compat (e : A ≃ₗ[K] W₀ × H)
    (pi : A →ₗ[K] W) (muA : P →ₗ[K] V →ₗ[K] A) (mu : P →ₗ[K] V →ₗ[K] W)
    (hmu : ∀ p v,pi (muA p v)=mu p v) (ell : W →ₗ[K] K) (p : P) (v : V) :
    ell (mu p v)=
      quotientSplitBottom e pi ell (splitTargetBottomAction e muA p v)+
      quotientSplitHigher e pi ell (splitTargetHigherAction e muA p v) := by
  rw [←hmu]
  exact quotientSplit_evaluation e pi ell (muA p v)

end Froberg
