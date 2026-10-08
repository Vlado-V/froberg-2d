import Froberg.ProductRows

/-! Polynomial product rows commute with every variable renaming. -/
noncomputable section
namespace Froberg.ProductRows
open Froberg MvPolynomial
variable {K : Type} [Field K] {σ τ : Type*}

theorem products_rename (e : ℕ → ℕ)
    (q : (j : ℕ) → Fin (e j) → MvPolynomial σ K) (f : σ → τ)
    {J R} (r : Row J R) (c : Columns e r) :
    products e (fun j i => rename f (q j i)) r c = rename f (products e q r c) := by
  classical
  by_cases h : r.val.val=R-r.val.val
  · unfold products
    simp only [dif_pos h]
    generalize hc : cast (if_pos h) c = p
    induction p using Sym2.inductionOn with
    | _ i j => exact (map_mul (rename f) (q _ i) (q _ j)).symm
  · unfold products
    simp only [dif_neg h]
    exact (map_mul (rename f) _ _).symm

theorem multiplication_rename (e : ℕ → ℕ)
    (q : (j : ℕ) → Fin (e j) → MvPolynomial σ K) (f : σ → τ) (J : Finset ℕ) (R : ℕ) :
    multiplication e (fun j i => rename f (q j i)) J R =
      (rename f).toLinearMap.comp (multiplication e q J R) := by
  rw [multiplication,multiplication,← Finsupp.linearCombination_linear_comp]
  congr 1
  funext p
  exact products_rename e q f p.1 p.2

theorem multiplication_rename_injective (e : ℕ → ℕ)
    (q : (j : ℕ) → Fin (e j) → MvPolynomial σ K) (f : σ ↪ τ) (J : Finset ℕ) (R : ℕ)
    (hq : Function.Injective (multiplication e q J R)) :
    Function.Injective (multiplication e (fun j i => rename f (q j i)) J R) := by
  rw [multiplication_rename]
  exact (rename_injective _ f.injective).comp hq

end Froberg.ProductRows
