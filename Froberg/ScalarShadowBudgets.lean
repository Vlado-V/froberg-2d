module

public import Froberg.BilinearCovectorStrata

@[expose] public section

/-! The strict-shadow inequality implies every scalar-surjectivity incidence
budget, including the zero and full kernel strata. -/
noncomputable section
namespace Froberg.BilinearCovectorStrata
open Module MvPolynomial Quartic

lemma covector_budget_of_strict_shadow {a r T q E : ℕ} (hr : r ≤ a)
    (R D : ℝ) (hT : (T : ℝ) = R*a) (hq : R ≤ q) (hD : (a : ℝ) ≤ D)
    (hE : R*r + D*(min r (a-r) : ℕ) ≤ E) :
    (r*(a-r) : ℕ)+(T : ℤ)-E-1 < (q*(a-r) : ℕ) := by
  have ho : ((r*(a-r) : ℕ) : ℝ) ≤ a*(min r (a-r) : ℕ) := by
    exact_mod_cast BilinearScalarFamily.grassmannian_overhead_le a r
  have hm := mul_le_mul_of_nonneg_right hD
    (Nat.cast_nonneg (min r (a-r)) : (0 : ℝ) ≤ _)
  have hslack := mul_nonneg (sub_nonneg.mpr hq)
    (Nat.cast_nonneg (a-r) : (0 : ℝ) ≤ _)
  have hsub : ((a-r : ℕ) : ℝ) = (a : ℝ)-r := Nat.cast_sub hr
  have hb : ((r*(a-r) : ℕ) : ℝ)+(T : ℝ)-E < (q*(a-r) : ℕ)+1 := by
    push_cast at ho hE hm ⊢
    rw [hsub] at ho hslack hE hm ⊢
    nlinarith
  have hbZ : (r*(a-r) : ℕ)+(T : ℤ)-E < (q*(a-r) : ℕ)+1 := by exact_mod_cast hb
  omega

/-- Scalar multiplication is generically surjective whenever qA≥T and the
strict gain is at least A. The rank bounds apply to the actual image subspaces. -/
theorem generic_surjective_of_strict_shadow {K : Type*} [Field K] [Infinite K]
    {a b T q : ℕ}
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (R D : ℝ) (hT : (T : ℝ) = R*a) (hq : R ≤ q) (hD : (a : ℝ) ≤ D)
    (hgrowth : ∀ L : Submodule K (Fin a → K),
      R*finrank K L + D*(min (finrank K L) (a-finrank K L) : ℕ) ≤
        finrank K (BilinearImage.image mu L)) :
    ∃ P : MvPolynomial (Fin q × Fin b) K,
      (∃ Q, eval Q P ≠ 0) ∧ ∀ Q, eval Q P ≠ 0 →
      Function.Surjective (BilinearScalarFamily.multiplication mu (fun i k => Q (i,k))) := by
  let E : Fin (a+1) → ℕ := fun r => ⌈R*r.val + D*(min r.val (a-r.val) : ℕ)⌉₊
  apply generic_surjective_of_budgets mu E
  · intro r L hL
    apply Nat.ceil_le.mpr
    simpa only [hL] using hgrowth L
  · intro r
    apply covector_budget_of_strict_shadow (by omega : r.val ≤ a) R D hT hq hD
    exact Nat.le_ceil _

end Froberg.BilinearCovectorStrata
