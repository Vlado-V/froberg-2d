import Quartic.PolynomialKernelAvoidance
import Quartic.PolynomialRankOpen

/-! Polynomial kernel avoidance in intrinsic finite-dimensional vector spaces. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic
variable {K I V W : Type*} [Field K] [Infinite K] [Fintype I]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- A polynomial family of linear equations with more independent equations
than parameters has a common nonempty principal open of avoiding vectors. -/
theorem polynomial_linear_kernel_avoidance (A : (I → K) → (V →ₗ[K] W))
    (hA : IsPolynomialFamily A) {r : ℕ} (hr : Fintype.card I < r) :
    ∃ P : MvPolynomial (Fin (finrank K V)) K,
      (∃ x, eval x P ≠ 0) ∧
      ∀ x, eval x P ≠ 0 → ∀ t,
        r ≤ finrank K (A t).range → A t ((Module.finBasis K V).equivFun.symm x) ≠ 0 := by
  classical
  let v := Module.finBasis K V
  let w := Module.finBasis K W
  have hentry (i : Fin (finrank K W)) (j : Fin (finrank K V)) :
      ∃ p : MvPolynomial I K, ∀ t, eval t p = w.repr (A t (v j)) i := by
    exact hA ((w.coord i).comp (LinearMap.applyₗ (R := K) (M₂ := W) (v j)))
  choose M hM using hentry
  have heval (t : I → K) : KernelPolynomialCharts.evaluated M t = LinearMap.toMatrix v w (A t) := by
    ext i j
    simpa only [KernelPolynomialCharts.evaluated,Matrix.map_apply,LinearMap.toMatrix_apply] using hM i j t
  obtain ⟨P,hP,havoid⟩ := PolynomialKernelAvoidance.principal_open_avoids_kernels M hr
  refine ⟨P,hP,?_⟩
  intro x hx t ht hz
  apply havoid x hx t
  · rw [heval,Matrix.rank_eq_finrank_range_toLin _ w v,Matrix.toLin_toMatrix]
    exact ht
  · rw [heval]
    have h := (A t).toMatrix_mulVec_repr v w (v.equivFun.symm x)
    change Matrix.mulVec (LinearMap.toMatrix v w (A t)) (v.equivFun (v.equivFun.symm x)) =
      w.equivFun (A t (v.equivFun.symm x)) at h
    rw [v.equivFun.apply_symm_apply,hz,map_zero] at h
    exact h

end Froberg
