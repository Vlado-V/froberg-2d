import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

/-! Weighted bipartite expansion, with the extra contribution of mixed targets.
The weights retain multiplicities of divisors of nonsquarefree monomials. -/
namespace Froberg

open Finset

/-- Counting a weighted cut, including one missing unit at each mixed target. -/
theorem weighted_cut_bound {S T : Type*} [Fintype S] [Fintype T]
    [DecidableEq S] [DecidableEq T]
    (w : T → S → ℕ) (A : Finset S) (B M : Finset T) (C L : ℕ)
    (hrow : ∀ t, ∑ s, w t s = C)
    (hcol : ∀ s, ∑ t, w t s = L)
    (hsupport : ∀ t ∉ B, ∀ s ∈ A, w t s = 0)
    (hMB : M ⊆ B)
    (hgap : ∀ t ∈ M, ∑ s ∈ A, w t s < C) :
    L * A.card + M.card ≤ C * B.card := by
  classical
  have hmass : (∑ t ∈ B, ∑ s ∈ A, w t s) = L * A.card := by
    calc
      (∑ t ∈ B, ∑ s ∈ A, w t s) = ∑ t : T, ∑ s ∈ A, w t s := by
        apply sum_subset (subset_univ B)
        intro t _ ht
        exact sum_eq_zero (fun s hs => hsupport t ht s hs)
      _ = ∑ s ∈ A, ∑ t : T, w t s := sum_comm
      _ = L * A.card := by simp [hcol, Nat.mul_comm]
  have hcount : (∑ t ∈ B, if t ∈ M then 1 else 0) = M.card := by
    rw [sum_boole, filter_mem_eq_inter, inter_eq_right.mpr hMB]
    norm_cast
  have hbound : ∀ t ∈ B, (∑ s ∈ A, w t s) + (if t ∈ M then 1 else 0) ≤ C := by
    intro t ht
    by_cases htm : t ∈ M
    · simpa [htm] using Nat.succ_le_iff.mpr (hgap t htm)
    · simp only [htm, ↓reduceIte, add_zero]
      calc
        (∑ s ∈ A, w t s) ≤ ∑ s : S, w t s := sum_le_sum_of_subset (subset_univ A)
        _ = C := hrow t
  have hh := sum_le_sum hbound
  simpa only [sum_add_distrib, hmass, hcount, sum_const, smul_eq_mul, Nat.mul_comm] using hh

/-- Row and column sums determine the total weight. -/
theorem weighted_total {S T : Type*} [Fintype S] [Fintype T]
    (w : T → S → ℕ) (C L : ℕ)
    (hrow : ∀ t, ∑ s, w t s = C)
    (hcol : ∀ s, ∑ t, w t s = L) :
    Fintype.card S * L = C * Fintype.card T := by
  calc
    Fintype.card S * L = ∑ s : S, ∑ t : T, w t s := by simp [hcol]
    _ = ∑ t : T, ∑ s : S, w t s := sum_comm
    _ = C * Fintype.card T := by simp [hrow, Nat.mul_comm]

/-- A bounded-fiber construction supplies the strict improvement over the
normalized shadow bound. All variables here are natural cardinalities. -/
theorem strengthened_weighted_expansion (N T k B M C L b u : ℕ)
    (hC : 0 < C) (hb : 0 < b)
    (htotal : N * L = C * T)
    (hcut : L * k + M ≤ C * B)
    (hfib : k * (N - k) * u ≤ b * M)
    (hu : C * b ≤ u) :
    T * k + N * k * (N - k) ≤ N * B := by
  have hmix : C * (k * (N - k)) ≤ M := by
    have h := Nat.mul_le_mul_left (k * (N - k)) hu
    nlinarith
  have hh : L * k + C * (k * (N - k)) ≤ C * B := by omega
  have hhN := Nat.mul_le_mul_left N hh
  have hident : N * (L * k) = (C * T) * k := by rw [← htotal]; ring
  nlinarith

/-- The finite bounded-fiber inequality in the form used for mixed monomials. -/
theorem card_le_mul_of_fiber_bound {S T : Type*} [DecidableEq S] [DecidableEq T]
    (A : Finset S) (B : Finset T) (f : S → T) (b : ℕ)
    (hf : ∀ a ∈ A, f a ∈ B)
    (hbound : ∀ t ∈ B, (A.filter (fun a => f a = t)).card ≤ b) :
    A.card ≤ b * B.card := by
  by_contra h
  have hh : B.card * b < A.card := by rw [Nat.mul_comm]; omega
  obtain ⟨t, ht, hlarge⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hh
  exact (not_lt_of_ge (hbound t ht)) hlarge

end Froberg
