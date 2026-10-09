module

public import Mathlib

@[expose] public section

/-! Lifting a finite profile transport through uniform couplings of its
fibers.  This is the exact normalization step in the monomial transport. -/
noncomputable section
namespace Froberg
open Finset
variable {I J : Type*} [Fintype I] [Fintype J]
variable {S : I → Type*} {T : J → Type*} [∀ i, Fintype (S i)] [∀ j, Fintype (T j)]

def fiberTransport (P : I → J → ℝ) (Q : ∀ i j, S i → T j → ℝ)
    (a : Σ i, S i) (b : Σ j, T j) : ℝ := P a.1 b.1 * Q a.1 b.1 a.2 b.2

theorem fiberTransport_row (P : I → J → ℝ) (Q : ∀ i j, S i → T j → ℝ)
    (p : I → ℝ) (hP : ∀ i, ∑ j, P i j = p i)
    (hQ : ∀ i j, P i j ≠ 0 → ∀ a, ∑ b, Q i j a b = 1 / (Fintype.card (S i) : ℝ))
    (a : Σ i, S i) :
    ∑ b : Σ j, T j, fiberTransport P Q a b = p a.1 / (Fintype.card (S a.1) : ℝ) := by
  rw [Fintype.sum_sigma]
  simp only [fiberTransport, ← mul_sum]
  have he (j : J) : P a.1 j * (∑ b, Q a.1 j a.2 b) =
      P a.1 j / (Fintype.card (S a.1) : ℝ) := by
    by_cases hz : P a.1 j = 0
    · simp [hz]
    · rw [hQ a.1 j hz a.2]
      ring
  simp only [he, ← sum_div, hP]

theorem fiberTransport_column (P : I → J → ℝ) (Q : ∀ i j, S i → T j → ℝ)
    (q : J → ℝ) (hP : ∀ j, ∑ i, P i j = q j)
    (hQ : ∀ i j, P i j ≠ 0 → ∀ b, ∑ a, Q i j a b = 1 / (Fintype.card (T j) : ℝ))
    (b : Σ j, T j) :
    ∑ a : Σ i, S i, fiberTransport P Q a b = q b.1 / (Fintype.card (T b.1) : ℝ) := by
  rw [Fintype.sum_sigma]
  simp only [fiberTransport, ← mul_sum]
  have he (i : I) : P i b.1 * (∑ a, Q i b.1 a b.2) =
      P i b.1 / (Fintype.card (T b.1) : ℝ) := by
    by_cases hz : P i b.1 = 0
    · simp [hz]
    · rw [hQ i b.1 hz b.2]
      ring
  simp only [he, ← sum_div, hP]

theorem fiberTransport_nonneg (P : I → J → ℝ) (Q : ∀ i j, S i → T j → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hQ : ∀ i j a b, 0 ≤ Q i j a b)
    (a : Σ i, S i) (b : Σ j, T j) : 0 ≤ fiberTransport P Q a b :=
  mul_nonneg (hP a.1 b.1) (hQ a.1 b.1 a.2 b.2)

theorem fiberTransport_lower (P : I → J → ℝ) (Q : ∀ i j, S i → T j → ℝ)
    (a : Σ i, S i) (b : Σ j, T j) (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hP : ε ≤ P a.1 b.1) (hQ : δ ≤ Q a.1 b.1 a.2 b.2) :
    ε * δ ≤ fiberTransport P Q a b :=
  mul_le_mul hP hQ hδ (hε.trans hP)

section Products
variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

/-- Tensoring two uniform finite couplings gives the product-fiber coupling. -/
def productTransport (P : A → B → ℝ) (Q : C → D → ℝ) (a : A × C) (b : B × D) : ℝ :=
  P a.1 b.1 * Q a.2 b.2

theorem productTransport_row (P : A → B → ℝ) (Q : C → D → ℝ)
    (hP : ∀ a, ∑ b, P a b = 1 / (Fintype.card A : ℝ))
    (hQ : ∀ c, ∑ d, Q c d = 1 / (Fintype.card C : ℝ)) (a : A × C) :
    ∑ b : B × D, productTransport P Q a b = 1 / (Fintype.card (A × C) : ℝ) := by
  simp only [Fintype.sum_prod_type, productTransport, ← mul_sum, hQ,
    ← sum_mul, hP, Fintype.card_prod, Nat.cast_mul]
  ring

theorem productTransport_column (P : A → B → ℝ) (Q : C → D → ℝ)
    (hP : ∀ b, ∑ a, P a b = 1 / (Fintype.card B : ℝ))
    (hQ : ∀ d, ∑ c, Q c d = 1 / (Fintype.card D : ℝ)) (b : B × D) :
    ∑ a : A × C, productTransport P Q a b = 1 / (Fintype.card (B × D) : ℝ) := by
  simp only [Fintype.sum_prod_type, productTransport, ← mul_sum, hQ,
    ← sum_mul, hP, Fintype.card_prod, Nat.cast_mul]
  ring

end Products
end Froberg
