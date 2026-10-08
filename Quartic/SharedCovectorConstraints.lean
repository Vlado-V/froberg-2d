import Quartic.CoefficientConstraintRank

/-!
# Shared child and auxiliary-target covector equations

The q actual child coefficient vectors and e separate auxiliary target
vectors are tested against one common covector. The exact codimension is
q*(a-d)+e for nonzero covector with true relation-kernel dimension d.
-/
noncomputable section
namespace Quartic.SharedCovectorConstraints
open Module BilinearCoefficientKernel BilinearCovectorCharts
variable {K : Type*} [Field K] {a b T q e : ℕ}

/-- Actual simultaneous equations on the shared child tuple and all auxiliary columns. -/
def constraint (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K)) (ell : Fin T → K) :
    ((Fin q → Fin b → K) × (Fin e → Fin T → K)) →ₗ[K]
      ((Fin q → Fin a → K) × (Fin e → K)) :=
  (CoefficientConstraintRank.repeated (coefficientMap mu ell)).prodMap
    (CoefficientConstraintRank.repeated (covector ell))

 theorem covector_ne_zero (ell : Fin T → K) (hell : ell ≠ 0) : covector ell ≠ 0 := by
  intro h
  apply hell
  apply covector_injective
  rw [h]
  ext x
  simp [covector_apply]

 theorem rank (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (ell : Fin T → K) (hell : ell ≠ 0) :
    finrank K (LinearMap.range (constraint (q := q) (e := e) mu ell)) =
      q * (a-finrank K (LinearMap.ker (relationMap mu ell))) + e := by
  rw [constraint,LinearMap.range_prodMap,(Submodule.prodEquiv _ _).finrank_eq,Module.finrank_prod,
    CoefficientConstraintRank.finrank_range,CoefficientConstraintRank.finrank_range]
  have hc : finrank K (LinearMap.range (coefficientMap mu ell)) =
      a-finrank K (LinearMap.ker (relationMap mu ell)) := by
    have h := coefficientMatrix_rank_eq mu ell
    rw [coefficientMatrix_eq_toMatrix,Matrix.rank] at h
    have he : (LinearMap.toMatrix' (coefficientMap mu ell)).mulVecLin = coefficientMap mu ell := by
      apply LinearMap.ext
      intro x
      exact LinearMap.toMatrix'_mulVec _ x
    rwa [he] at h
  rw [hc,Module.Dual.range_eq_top_of_ne_zero (covector_ne_zero ell hell),finrank_top,
    Module.finrank_self,Nat.mul_one]

 theorem kernel_iff (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (ell : Fin T → K) (Q : Fin q → Fin b → K) (Z : Fin e → Fin T → K) :
    constraint mu ell (Q,Z) = 0 ↔
      (∀ i v, covector ell (mu (Q i) v) = 0) ∧ (∀ j, covector ell (Z j) = 0) := by
  constructor
  · intro h
    have hQ := congrArg Prod.fst h
    have hZ := congrArg Prod.snd h
    constructor
    · intro i
      apply (coefficientMatrix_kernel_iff mu ell (Q i)).mp
      rw [coefficientMatrix_mulVec]
      exact congrFun hQ i
    · intro j
      exact congrFun hZ j
  · rintro ⟨hQ,hZ⟩
    apply Prod.ext
    · funext i
      have h := (coefficientMatrix_kernel_iff mu ell (Q i)).mpr (hQ i)
      rwa [coefficientMatrix_mulVec] at h
    · funext j
      exact hZ j

end Quartic.SharedCovectorConstraints
