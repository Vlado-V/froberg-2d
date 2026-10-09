module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

@[expose] public section

/-! Summing the uniform exceptional projection losses over all source fibers. -/
namespace Froberg.ExceptionBudget
open Finset
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Nonzero proper source fibers consume both dimension and codimension. -/
theorem card_proper_le_min (d l : I → ℕ) (hl : ∀ i, l i ≤ d i) :
    (univ.filter (fun i => 0 < l i ∧ l i < d i)).card ≤
      min (∑ i, l i) ((∑ i, d i) - ∑ i, l i) := by
  let P := univ.filter (fun i => 0 < l i ∧ l i < d i)
  have hleft : P.card ≤ ∑ i, l i := by
    calc
      P.card = ∑ i ∈ P, 1 := by simp
      _ ≤ ∑ i ∈ P, l i := sum_le_sum (fun i hi => (mem_filter.mp hi).2.1)
      _ ≤ ∑ i, l i := sum_le_sum_of_subset (filter_subset _ _)
  have hright : P.card ≤ ∑ i, (d i-l i) := by
    calc
      P.card = ∑ i ∈ P, 1 := by simp
      _ ≤ ∑ i ∈ P, (d i-l i) := sum_le_sum (fun i hi => by
        have hh := (mem_filter.mp hi).2.2
        omega)
      _ ≤ ∑ i, (d i-l i) := sum_le_sum_of_subset (filter_subset _ _)
  have hsum : (∑ i, (d i-l i)) + ∑ i, l i = ∑ i, d i := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun i _ => Nat.sub_add_cancel (hl i))
  change P.card ≤ min (∑ i, l i) ((∑ i, d i) - ∑ i, l i)
  exact le_min hleft (by omega)

/-- A uniform exception count per proper source fiber gives a loss proportional
to the smaller of total dimension and total codimension. -/
theorem sum_loss_le (d l : I → ℕ) (hl : ∀ i, l i ≤ d i)
    (E : I → Finset J) (C h : ℕ)
    (hE : ∀ i, 0 < l i → l i < d i → (E i).card ≤ C)
    (ideal actual : J → ℕ) (hideal : ∀ j, ideal j ≤ h)
    (hgood : ∀ j, (∀ i, 0 < l i → l i < d i → j ∉ E i) → ideal j ≤ actual j) :
    (∑ j, ideal j) ≤ (∑ j, actual j) +
      h * C * min (∑ i, l i) ((∑ i, d i) - ∑ i, l i) := by
  classical
  let P := univ.filter (fun i => 0 < l i ∧ l i < d i)
  let B := P.biUnion E
  have hB : B.card ≤ C * min (∑ i, l i) ((∑ i, d i) - ∑ i, l i) := by
    calc
      B.card ≤ P.card*C := card_biUnion_le_card_mul P E C (fun i hi =>
        hE i (mem_filter.mp hi).2.1 (mem_filter.mp hi).2.2)
      _ ≤ min (∑ i, l i) ((∑ i, d i) - ∑ i, l i)*C :=
        Nat.mul_le_mul_right C (card_proper_le_min d l hl)
      _ = _ := Nat.mul_comm _ _
  have hpoint : ∀ j, ideal j ≤ actual j + if j ∈ B then h else 0 := by
    intro j
    by_cases hj : j ∈ B
    · simp only [hj,ite_true]
      exact (hideal j).trans (Nat.le_add_left _ _)
    · simp only [hj,ite_false,add_zero]
      apply hgood j
      intro i hi0 hid hji
      exact hj (mem_biUnion.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hi0,hid⟩,hji⟩)
  have hsum := sum_le_sum (fun j (_ : j ∈ (univ : Finset J)) => hpoint j)
  have hind : (∑ j : J, if j ∈ B then h else 0) = B.card*h := by
    rw [← sum_filter]
    simp
  rw [sum_add_distrib,hind] at hsum
  have hm := Nat.mul_le_mul_left h hB
  nlinarith

end Froberg.ExceptionBudget
