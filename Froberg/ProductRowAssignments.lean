import Froberg.ProductRowProfiles

/-! Common-family assembly while retaining every imposed layer constraint. -/
noncomputable section
namespace Froberg.ProductRows
open Froberg MvPolynomial
variable {K : Type} [Field K] {σ : Type*}

theorem exists_cross_assignment (e : ℕ → ℕ) {j l : ℕ} (hjl : j≠l)
    (P : (a : ℕ) → (Fin (e a) → MvPolynomial σ K) → Prop)
    (hzero : ∀ a, P a 0)
    (f : Fin (e j) → MvPolynomial σ K) (g : Fin (e l) → MvPolynomial σ K)
    (hf : P j f) (hg : P l g) :
    ∃ q : (a : ℕ) → Fin (e a) → MvPolynomial σ K,
      (∀ a, P a (q a)) ∧ q j=f ∧ q l=g := by
  classical
  let q : (a : ℕ) → Fin (e a) → MvPolynomial σ K :=
    Function.update (Function.update (fun _ => 0) l g) j f
  have hleft : q j=f := Function.update_self _ _ _
  have hright : q l=g := by simp only [q,Function.update_of_ne hjl.symm,Function.update_self]
  refine ⟨q,?_,hleft,hright⟩
  intro a
  by_cases haj : a=j
  · subst a; simpa only [hleft] using hf
  · by_cases hal : a=l
    · subst a; simpa only [hright] using hg
    · simpa only [q,Function.update_of_ne haj,Function.update_of_ne hal] using hzero a

theorem exists_diagonal_assignment (e : ℕ → ℕ) (j : ℕ)
    (P : (a : ℕ) → (Fin (e a) → MvPolynomial σ K) → Prop)
    (hzero : ∀ a, P a 0) (f : Fin (e j) → MvPolynomial σ K) (hf : P j f) :
    ∃ q : (a : ℕ) → Fin (e a) → MvPolynomial σ K,
      (∀ a, P a (q a)) ∧ q j=f := by
  classical
  let q : (a : ℕ) → Fin (e a) → MvPolynomial σ K := Function.update (fun _ => 0) j f
  have hleft : q j=f := Function.update_self _ _ _
  refine ⟨q,?_,hleft⟩
  intro a
  by_cases haj : a=j
  · subst a; simpa only [hleft] using hf
  · simpa only [q,Function.update_of_ne haj] using hzero a

/-- Every constraint holds for the same common family used in all blocks. -/
theorem exists_injective_product_row_with_conditions
    (e : ℕ → ℕ) (w : σ → ℕ) {J : Finset ℕ} {R : ℕ}
    (P : (a : ℕ) → (Fin (e a) → MvPolynomial σ K) → Prop)
    (hzero : ∀ a, P a 0) (heven : ∀ j ∈ J, Even j)
    (hweight : ∀ q : (a : ℕ) → Fin (e a) → MvPolynomial σ K,
      (∀ a, P a (q a)) → ∀ j∈J, ∀ i, (q j i).IsWeightedHomogeneous w (assignedDegree R j))
    (hlocal : ∀ r : Row J R,
      ∃ q : (a : ℕ) → Fin (e a) → MvPolynomial σ K,
        (∀ a, P a (q a)) ∧ LinearIndependent K (products e q r)) :
    ∃ q : (a : ℕ) → Fin (e a) → MvPolynomial σ K,
      (∀ a, P a (q a)) ∧ Function.Injective (multiplication e q J R) := by
  classical
  choose q hq hi using hlocal
  have hall : ∀ a, P a (assembledFamily e q a) := by
    intro a
    unfold assembledFamily
    split_ifs with h
    · exact hq h.choose a
    · exact hzero a
  refine ⟨assembledFamily e q,hall,?_⟩
  apply multiplication_injective e _ w J R heven (hweight _ hall)
  intro r
  rw [assembled_products]
  exact hi r

end Froberg.ProductRows
