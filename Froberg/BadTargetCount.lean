module

public import Froberg.MonomialIncidence

@[expose] public section

/-! A direct substitute for the small-defect monomial growth estimate in B.2.
Splitting a target into two source monomials and one variable suffices. -/
namespace Froberg
open Finset MonomialExpansion

/-- If every degree-`s` divisor of every degree-`2s+1` target belongs to `B`,
there are at most `|B|² n` such targets. -/
theorem card_bad_targets_le_square_mul {n s : ℕ}
    (B T : Finset (Fin n →₀ ℕ))
    (hdeg : ∀ x ∈ T, x.degree = 2 * s + 1)
    (hdiv : ∀ x ∈ T, ∀ a : Fin n →₀ ℕ, a.degree = s → a ≤ x → a ∈ B) :
    T.card ≤ B.card ^ 2 * n := by
  classical
  let A := (B ×ˢ B) ×ˢ exponents n 1
  let f : ((Fin n →₀ ℕ) × (Fin n →₀ ℕ)) × (Fin n →₀ ℕ) → (Fin n →₀ ℕ) :=
    fun p => p.1.1 + p.1.2 + p.2
  have hsub : T ⊆ A.image f := by
    intro x hx
    obtain ⟨a, ha, has⟩ := Finsupp.exists_le_degree_eq x s (by rw [hdeg x hx]; omega)
    have hrem : (x - a).degree = s + 1 := by
      have he := congrArg Finsupp.degree (tsub_add_cancel_of_le ha)
      rw [map_add, has, hdeg x hx] at he
      omega
    obtain ⟨b, hb, hbs⟩ := Finsupp.exists_le_degree_eq (x - a) s (by rw [hrem]; omega)
    have hc : (x - a - b).degree = 1 := by
      have he := congrArg Finsupp.degree (tsub_add_cancel_of_le hb)
      rw [map_add, hbs, hrem] at he
      omega
    have haB := hdiv x hx a has ha
    have hbB := hdiv x hx b hbs (hb.trans tsub_le_self)
    refine mem_image.mpr ⟨((a, b), x - a - b), ?_, ?_⟩
    · exact mem_product.mpr ⟨mem_product.mpr ⟨haB, hbB⟩, mem_exponents.mpr hc⟩
    · change a + b + (x - a - b) = x
      rw [add_assoc, add_tsub_cancel_of_le hb, add_tsub_cancel_of_le ha]
  calc
    T.card ≤ (A.image f).card := card_le_card hsub
    _ ≤ A.card := card_image_le
    _ = B.card ^ 2 * n := by simp [A, card_exponents, pow_two]

/-- For small source defect, the preceding quadratic count has the required
linear bound at scale `m^(s+1)`. This form avoids fractional powers. -/
theorem bad_target_small_defect_bound (m s h k : ℕ) (δ : ℝ)
    (hk : (k : ℝ) ≤ δ * (m : ℝ) ^ s) :
    ((h * (k ^ 2 * m) : ℕ) : ℝ) ≤ (h : ℝ) * δ * (m : ℝ) ^ (s + 1) * k := by
  push_cast
  have hh := mul_le_mul_of_nonneg_right hk (show 0 ≤ (h : ℝ) * k * m by positivity)
  rw [pow_succ (m : ℝ) s]
  convert hh using 1 <;> ring

end Froberg
