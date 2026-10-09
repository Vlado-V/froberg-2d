module

public import Froberg.EvenReductionRename

@[expose] public section

/-! Independent leading layers survive a bijection of output variables. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ τ : Type*} [Fintype σ] [Fintype τ]
variable {n d q : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem leading_independent_output_rename (e : σ ≃ τ)
    (p : Space n d q J counts O) (j : J) (hp : LinearIndependent K (p.2 j)) :
    LinearIndependent K ((outputRename e p).2 j) := by
  have h₀ := hp.map' (biformImage (O j.val) (Forms K n (d-j.val))).subtype
    (Submodule.ker_subtype _)
  have h₁ := h₀.map' (rename (Sum.map e id)).toLinearMap
    (LinearMap.ker_eq_bot.mpr (rename_injective _
      (Function.Injective.sumMap e.injective (fun _ _ h => h))))
  apply LinearIndependent.of_comp
    (biformImage ((O j.val).map (rename e).toLinearMap) (Forms K n (d-j.val))).subtype
  exact h₁

theorem leading_witnesses_output_rename (e : σ ≃ τ)
    (hw : ∀ j : J,∃ p : Space n d q J counts O,LinearIndependent K (p.2 j)) :
    ∀ j : J,∃ p : Space n d q J counts (fun j => (O j).map (rename e).toLinearMap),
      LinearIndependent K (p.2 j) := by
  intro j
  obtain ⟨p,hp⟩ := hw j
  exact ⟨outputRename e p,leading_independent_output_rename e p j hp⟩

theorem leading_witnesses_congr_outputs
    {O O' : ℕ → Submodule K (MvPolynomial σ K)} (hO : O=O') :
    (∀ j : J,∃ p : Space n d q J counts O,LinearIndependent K (p.2 j)) ↔
      (∀ j : J,∃ p : Space n d q J counts O',LinearIndependent K (p.2 j)) := by
  subst O'
  rfl

theorem leading_witnesses_congr_counts
    {counts counts' : ℕ → ℕ} (O : ℕ → Submodule K (MvPolynomial σ K))
    (hcounts : counts=counts') :
    (∀ j : J,∃ p : Space n d q J counts O,LinearIndependent K (p.2 j)) ↔
      (∀ j : J,∃ p : Space n d q J counts' O,LinearIndependent K (p.2 j)) := by
  subst counts'
  rfl

theorem leading_witnesses_constraint_rename
    {X : Type*} [AddCommGroup X] [Module K X]
    (T : ℕ → MvPolynomial τ K →ₗ[K] X) (e : σ ≃ τ)
    (hw : ∀ j : J,∃ p : Space n d q J counts
      (fun k => homogeneousSubmodule σ K k ⊓ ((T k).comp (rename e).toLinearMap).ker),
      LinearIndependent K (p.2 j)) :
    ∀ j : J,∃ p : Space n d q J counts
      (fun k => homogeneousSubmodule τ K k ⊓ (T k).ker),LinearIndependent K (p.2 j) := by
  have hmap : (fun k => (homogeneousSubmodule σ K k ⊓
      ((T k).comp (rename e).toLinearMap).ker).map (rename e).toLinearMap)=
      (fun k => homogeneousSubmodule τ K k ⊓ (T k).ker) := by
    funext k
    exact homogeneous_kernel_rename_eq e (T k) k
  have H := leading_witnesses_output_rename e hw
  exact (leading_witnesses_congr_outputs hmap).mp H

end Froberg.PreparedParameters
