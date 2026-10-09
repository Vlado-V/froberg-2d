module

public import Froberg.ClosedBaseParameters
public import Froberg.SecondStageSlices

@[expose] public section

/-! Graph parameters over a sliced algebraic base, with all constrained
first-stage vectors quantified and only the common final parameters chosen. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open MvPolynomial Matrix Quartic Quartic.KernelPolynomialCharts
variable {K : Type*} [Field K] [Infinite K]
variable {q N s fcount a b n l r₁ r₂ : ℕ}

theorem principal_open_second_dehom_with_parameters
    {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
    (degrees : Fin fcount → ℕ) (f : ∀ i,Forms K q (degrees i))
    (ell : Fin (s+1) → Forms K q 1)
    (hempty : ∀ t : Fin q → L,(∀ i,aeval t (f i).val=0) →
      (∀ j,aeval t (ell j).val=0) → t=0)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial (Fin (q+N)) K))
    (B : Matrix (Fin b) (Fin l) (MvPolynomial (Fin (q+N) ⊕ Fin n) K))
    (hcount : s+N+n<r₁+r₂) :
    ∃ P : MvPolynomial (Fin l) K,
      (∃ z,eval z P≠0) ∧ ∀ z,eval z P≠0 →
        ∀ (x : Fin n → K) (t : Fin q → K),
          (∀ i,eval t (f i).val=0) → eval t (ell 0).val=1 → ∀ u : Fin N → K,
          r₁≤(evaluated A (Fin.append t u)).rank →
          r₂≤(evaluated B (Sum.elim (Fin.append t u) x)).rank →
          evaluated A (Fin.append t u) *ᵥ x≠0 ∨
            evaluated B (Sum.elim (Fin.append t u) x) *ᵥ z≠0 := by
  obtain ⟨P,hP,hgood⟩ := SliceMotionAvoidance.principal_open_second_dehom
    degrees (fun i => liftBaseForm (N := N) (f i)) (baseParameterSlices (N := N) ell)
    (baseParameterSlices_empty degrees f ell hempty) A B hcount
  refine ⟨P,hP,?_⟩
  intro z hz x t hf hell u
  apply hgood z hz x (Fin.append t u)
  · intro i
    simpa only [eval_liftBaseForm,Fin.append_left] using hf i
  · simpa only [baseParameterSlices,Fin.cons_zero,eval_liftBaseForm,Fin.append_left] using hell

end Froberg
