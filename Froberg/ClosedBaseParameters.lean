import Froberg.Graded
import Quartic.SliceMotionAvoidance

/-! Freely adjoining profile-chart and higher-covector parameters to a
closed sliced base. The dimension cost is exactly the number of new parameters. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open MvPolynomial Matrix Quartic Quartic.KernelPolynomialCharts
variable {K : Type*} [Field K] {q N s fcount d a b n l r₁ r₂ : ℕ}

def liftBaseForm (f : Forms K q d) : Forms K (q+N) d :=
  ⟨rename (Fin.castAdd N) f.val,f.property.rename_isHomogeneous⟩

def freeParameterForm (i : Fin N) : Forms K (q+N) 1 :=
  ⟨X (Fin.natAdd q i),isHomogeneous_X K (Fin.natAdd q i)⟩

def baseParameterSlices (ell : Fin (s+1) → Forms K q 1) :
    Fin (s+N+1) → Forms K (q+N) 1 :=
  Fin.cons (liftBaseForm (N := N) (ell 0))
    (Fin.append (fun i : Fin s => liftBaseForm (N := N) (ell i.succ)) freeParameterForm)

@[simp] lemma eval_liftBaseForm (f : Forms K q d) (t : Fin (q+N) → K) :
    eval t (liftBaseForm (N := N) f).val=eval (fun i => t (Fin.castAdd N i)) f.val := by
  exact eval_rename _ _ _

lemma baseParameterSlices_empty {L : Type*} [Field L] [Algebra K L]
    (degrees : Fin fcount → ℕ) (f : ∀ i, Forms K q (degrees i))
    (ell : Fin (s+1) → Forms K q 1)
    (hempty : ∀ t : Fin q → L, (∀ i, aeval t (f i).val=0) →
      (∀ j, aeval t (ell j).val=0) → t=0) :
    ∀ t : Fin (q+N) → L, (∀ i, aeval t (liftBaseForm (N := N) (f i)).val=0) →
      (∀ j, aeval t (baseParameterSlices (N := N) ell j).val=0) → t=0 := by
  intro t hf hell
  let t0 : Fin q → L := fun i => t (Fin.castAdd N i)
  have ht0 : t0=0 := by
    apply hempty t0
    · intro i
      simpa only [liftBaseForm,aeval_rename,Function.comp_def] using hf i
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [baseParameterSlices,Fin.cons_zero,liftBaseForm,aeval_rename,
          Function.comp_def] using hell 0
      · simpa only [baseParameterSlices,Fin.cons_succ,Fin.append_left,liftBaseForm,
          aeval_rename,Function.comp_def] using hell ((Fin.castAdd N j).succ)
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact congrFun ht0 j
  · have h := hell ((Fin.natAdd s j).succ)
    simpa only [baseParameterSlices,Fin.cons_succ,Fin.append_right,freeParameterForm,
      aeval_X,Pi.zero_apply] using h

/-- The actual algebraic slice theorem remains valid after adjoining N
arbitrary parameters, with exactly N additional units in its dimension budget. -/
theorem principal_open_dehom_with_parameters [Infinite K]
    {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
    (degrees : Fin fcount → ℕ) (f : ∀ i, Forms K q (degrees i))
    (ell : Fin (s+1) → Forms K q 1)
    (hempty : ∀ t : Fin q → L, (∀ i, aeval t (f i).val=0) →
      (∀ j, aeval t (ell j).val=0) → t=0)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial (Fin (q+N)) K))
    (B : Matrix (Fin b) (Fin l) (MvPolynomial (Fin (q+N) ⊕ Fin n) K))
    (hcount : s+N<r₁+r₂) :
    ∃ P : MvPolynomial (Fin n ⊕ Fin l) K,
      (∃ z, eval z P ≠ 0) ∧ ∀ z, eval z P ≠ 0 →
        ∀ t : Fin q → K, (∀ i,eval t (f i).val=0) → eval t (ell 0).val=1 →
        ∀ u : Fin N → K,
          r₁ ≤ (evaluated A (Fin.append t u)).rank →
          r₂ ≤ (evaluated B (Sum.elim (Fin.append t u) (fun i => z (.inl i)))).rank →
          Matrix.mulVec (evaluated A (Fin.append t u)) (fun i => z (.inl i)) ≠ 0 ∨
          Matrix.mulVec (evaluated B (Sum.elim (Fin.append t u) (fun i => z (.inl i))))
            (fun j => z (.inr j)) ≠ 0 := by
  obtain ⟨P,hP,hgood⟩ := SliceMotionAvoidance.principal_open_dehom
    degrees (fun i => liftBaseForm (N := N) (f i)) (baseParameterSlices (N := N) ell)
    (baseParameterSlices_empty degrees f ell hempty) A B hcount
  refine ⟨P,hP,?_⟩
  intro z hz t hf hell u
  apply hgood z hz (Fin.append t u)
  · intro i
    simpa only [eval_liftBaseForm,Fin.append_left] using hf i
  · simpa only [baseParameterSlices,Fin.cons_zero,eval_liftBaseForm,Fin.append_left] using hell

end Froberg
