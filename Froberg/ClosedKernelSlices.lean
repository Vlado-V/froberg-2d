module

public import Quartic.AmbientCovectorSpreading

@[expose] public section

/-! Homogeneous equations for the actual closed relation-kernel thresholds. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Quartic BilinearCovectorCharts BilinearCoefficientKernel
variable {K : Type*} [Field K] {a b T : ℕ}

theorem exists_closed_kernel_slices
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (s : ℕ → ℕ) (Z : (r : Fin (a+1)) → Fin (s r.val) → Fin T → K)
    (hZ : ∀ r : Fin (a+1),∀ ell : Fin T → K,
      r.val ≤ finrank K (LinearMap.ker (relationMap mu ell)) →
      (∀ t,covector ell (Z r t)=0) → ell=0) :
    ∃ (count : Fin (a+1) → ℕ) (degrees : ∀ r,Fin (count r) → ℕ)
      (eqs : ∀ r,(i : Fin (count r)) → Forms K T (degrees r i))
      (cuts : ∀ r : Fin (a+1),Fin (s r.val) → Forms K T 1),
      (∀ r (ell : Fin T → K),(∀ i,eval ell (eqs r i).val=0) ↔
        r.val ≤ finrank K (LinearMap.ker (relationMap mu ell))) ∧
      (∀ r (ell : Fin T → K),(∀ i,aeval ell (eqs r i).val=0) →
        (∀ t,aeval ell (cuts r t).val=0) → ell=0) := by
  let count : Fin (a+1) → ℕ := fun r => Fintype.card (AmbientCovectorSpreading.Index a b 0 0 r.val)
  let deg : ∀ r : Fin (a+1),Fin (count r) → ℕ := fun r =>
    AmbientCovectorSpreading.finiteDegree a b 0 0 r.val
  let eqs : ∀ r : Fin (a+1),(i : Fin (count r)) → Forms K T (deg r i) := fun r =>
    AmbientCovectorSpreading.finiteOriginalEquations (d := r.val) mu
      (0 : Fin 0 → Fin a → K) (0 : Fin 0 → Fin b → K)
  have heq (r : Fin (a+1)) (ell : Fin T → K) :
      (∀ i,eval ell (eqs r i).val=0) ↔
        r.val ≤ finrank K (LinearMap.ker (relationMap mu ell)) := by
    have hh := AmbientCovectorSpreading.finite_original_equations_iff
      (d := r.val) mu (0 : Fin 0 → Fin a → K) (0 : Fin 0 → Fin b → K)
      (by omega) ell
    simpa only [eqs,Nat.add_zero,Fin.forall_fin_zero,true_and,and_true] using hh
  refine ⟨count,deg,eqs,fun r => AmbientCovectorSpreading.slices (Z r),heq,?_⟩
  intro r ell he hc
  apply hZ r ell ((heq r ell).mp (by simpa only [aeval_eq_eval] using he))
  intro t
  simpa only [AmbientCovectorSpreading.slices,aeval_eq_eval,
    ClosedCovectorEquations.eval_linearForm] using hc t

end Froberg
