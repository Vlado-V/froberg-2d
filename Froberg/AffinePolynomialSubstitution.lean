module

public import Quartic.MiddleCoordinates

@[expose] public section

/-! Pulling a principal open back along an affine parameter map. -/
noncomputable section
namespace Froberg
open MvPolynomial
variable {K ι τ : Type*} [Field K] [Fintype τ] [DecidableEq τ]

def substituteAffine (F : (τ → K) →ₗ[K] (ι → K)) (c : ι → K) :
    MvPolynomial ι K →ₐ[K] MvPolynomial τ K :=
  aeval (fun i => Quartic.polynomialOfLinear ((LinearMap.proj i).comp F)+C (c i))

lemma eval_substituteAffine (F : (τ → K) →ₗ[K] (ι → K)) (c : ι → K)
    (x : τ → K) (P : MvPolynomial ι K) :
    eval x (substituteAffine F c P)=eval (F x+c) P := by
  have hh : (aeval x).comp (substituteAffine F c)=aeval (F x+c) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply,substituteAffine,aeval_X,map_add,aeval_C]
    rw [aeval_eq_eval,Quartic.eval_polynomialOfLinear]
    rfl
  exact congrArg (fun f : MvPolynomial ι K →ₐ[K] K => f P) hh

end Froberg
