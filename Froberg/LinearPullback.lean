import Froberg.Generic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RepresentationTheory.Basic

/-! # Polynomial pullback by linear changes of coefficient coordinates -/

noncomputable section
namespace Froberg
open MvPolynomial

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

/-- A linear change of affine coordinates acts on their polynomial ring. -/
def linearPullback (L : (I → K) →ₗ[K] (I → K)) :
    MvPolynomial I K →ₐ[K] MvPolynomial I K :=
  aeval (fun i => polynomialOfLinear ((LinearMap.proj i).comp L))

@[simp] theorem linearPullback_eval (L : (I → K) →ₗ[K] (I → K))
    (a : I → K) (P : MvPolynomial I K) :
    eval a (linearPullback L P) = eval (L a) P := by
  have hh : (eval a).comp (linearPullback L).toRingHom = eval (L a) := by
    ext c i <;> simp [linearPullback, eval_polynomialOfLinear]
  exact RingHom.congr_fun hh P

variable [Infinite K]

@[simp] theorem linearPullback_id :
    linearPullback (LinearMap.id : (I → K) →ₗ[K] (I → K)) =
      AlgHom.id K (MvPolynomial I K) := by
  ext1 P
  apply MvPolynomial.funext
  intro a
  simp

/-- Pullback reverses the composition of coordinate maps. -/
theorem linearPullback_comp (L M : (I → K) →ₗ[K] (I → K)) :
    linearPullback (L.comp M) = (linearPullback M).comp (linearPullback L) := by
  ext1 P
  apply MvPolynomial.funext
  intro a
  simp

/-- An invertible linear coordinate change has an invertible polynomial
pullback, with the expected formula at every point. -/
def linearPullbackEquiv (L : (I → K) ≃ₗ[K] (I → K)) :
    MvPolynomial I K ≃ₐ[K] MvPolynomial I K :=
  AlgEquiv.ofAlgHom (linearPullback L.toLinearMap) (linearPullback L.symm.toLinearMap)
    (by rw [← linearPullback_comp, L.symm_comp, linearPullback_id])
    (by rw [← linearPullback_comp, L.comp_symm, linearPullback_id])

@[simp] theorem linearPullbackEquiv_eval (L : (I → K) ≃ₗ[K] (I → K))
    (a : I → K) (P : MvPolynomial I K) :
    eval a (linearPullbackEquiv L P) = eval (L a) P :=
  linearPullback_eval L.toLinearMap a P

/-- The automorphism associated to an element of a representation. -/
def representationLinearEquiv {G V : Type*} [Group G]
    [AddCommGroup V] [Module K V] (ρ : Representation K G V) (g : G) : V ≃ₗ[K] V where
  toFun := ρ g
  invFun := ρ g⁻¹
  left_inv := ρ.inv_self_apply g
  right_inv := ρ.self_inv_apply g
  map_add' := (ρ g).map_add
  map_smul' := (ρ g).map_smul

/-- A linear representation on affine coordinates induces an honest
action on their polynomial ring by inverse pullback. -/
def representationPullback {G : Type*} [Group G] (ρ : Representation K G (I → K)) :
    G →* (MvPolynomial I K ≃ₐ[K] MvPolynomial I K) where
  toFun g := linearPullbackEquiv (representationLinearEquiv ρ g⁻¹)
  map_one' := by
    apply AlgEquiv.ext
    intro P
    apply MvPolynomial.funext
    intro a
    simp [linearPullbackEquiv_eval, representationLinearEquiv]
  map_mul' g h := by
    apply AlgEquiv.ext
    intro P
    apply MvPolynomial.funext
    intro a
    simp [linearPullbackEquiv_eval, representationLinearEquiv, map_mul,
      Module.End.mul_apply]

@[simp] theorem representationPullback_eval {G : Type*} [Group G]
    (ρ : Representation K G (I → K)) (g : G) (a : I → K) (P : MvPolynomial I K) :
    eval a (representationPullback ρ g P) = eval (ρ g⁻¹ a) P :=
  linearPullbackEquiv_eval _ _ _

end Froberg
