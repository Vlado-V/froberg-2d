import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic

/-! Covectors on a quotient by triangular polynomial relations are determined
by their bottom component. This is the elimination step used after the
homogeneous bidegree target surjections in B.7 and C.4. -/
noncomputable section
namespace Froberg
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}
variable {V S : Fin (n+1) → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  [∀ i, AddCommGroup (S i)] [∀ i, Module K (S i)]

/-- Evaluation of a linear covector is the sum of its component evaluations. -/
theorem covector_sum_components (ell : ((i : Fin (n+1)) → V i) →ₗ[K] K)
    (x : (i : Fin (n+1)) → V i) :
    ell x = ∑ i, ell (Pi.single i (x i)) := by
  classical
  have hx : (∑ i, Pi.single i (x i)) = x := by
    funext j
    simp
  calc
    ell x = ell (∑ i, Pi.single i (x i)) := congrArg ell hx.symm
    _ = ∑ i, ell (Pi.single i (x i)) := map_sum _ _ _

/-- Lower terms in a relation do not obstruct induction once the leading
bidegree maps are onto. No independence of the lower relations is assumed. -/
theorem triangular_covector_zero
    (C : (i : Fin (n+1)) → S i →ₗ[K] ((j : Fin (n+1)) → V j))
    (hupper : ∀ i j, i < j → ∀ s, C i s j = 0)
    (hsurj : ∀ i, i ≠ 0 → Function.Surjective (fun s => C i s i))
    (ell : ((i : Fin (n+1)) → V i) →ₗ[K] K)
    (hann : ∀ i, i ≠ 0 → ∀ s, ell (C i s) = 0)
    (hbottom : ∀ x : V 0, ell (Pi.single 0 x) = 0) : ell = 0 := by
  classical
  have hcomponent : ∀ i : Fin (n+1), ∀ x : V i, ell (Pi.single i x) = 0 := by
    intro i
    induction i using Fin.strong_induction_on with
    | h i ih =>
      intro x
      by_cases hi : i = 0
      · subst i
        exact hbottom x
      obtain ⟨s,hs⟩ := hsurj i hi x
      change C i s i = x at hs
      have he := covector_sum_components ell (C i s)
      rw [hann i hi s] at he
      have hsum : (∑ j, ell (Pi.single j (C i s j))) = ell (Pi.single i x) := by
        rw [Finset.sum_eq_single i]
        · rw [hs]
        · intro j _ hji
          rcases lt_or_gt_of_ne hji with hj | hj
          · exact ih j hj _
          · rw [hupper i j hj,Pi.single_zero,map_zero]
        · simp
      rw [hsum] at he
      exact he.symm
  apply LinearMap.ext
  intro x
  rw [covector_sum_components]
  simp only [hcomponent,Finset.sum_const_zero,LinearMap.zero_apply]

/-- Two quotient covectors agreeing on the bottom target agree everywhere. -/
theorem triangular_covector_ext
    (C : (i : Fin (n+1)) → S i →ₗ[K] ((j : Fin (n+1)) → V j))
    (hupper : ∀ i j, i < j → ∀ s, C i s j = 0)
    (hsurj : ∀ i, i ≠ 0 → Function.Surjective (fun s => C i s i))
    (ell eta : ((i : Fin (n+1)) → V i) →ₗ[K] K)
    (hell : ∀ i, i ≠ 0 → ∀ s, ell (C i s) = 0)
    (heta : ∀ i, i ≠ 0 → ∀ s, eta (C i s) = 0)
    (hbottom : ∀ x : V 0, ell (Pi.single 0 x) = eta (Pi.single 0 x)) : ell = eta := by
  apply sub_eq_zero.mp
  apply triangular_covector_zero C hupper hsurj
  · intro i hi s
    simp [hell i hi s,heta i hi s]
  · intro x
    simp [hbottom x]

end Froberg
