import Froberg.PrivateColumns

/-! Exact overlaps of the distinct private powers. These assertions use the
literal monomial exponents, including the unique two-column overlap target. -/
noncomputable section
namespace Froberg.PrivateColumns
open Finset
variable {a z s b : ℕ}

/-- Distinct private powers occupy disjoint coordinates. -/
theorem private_pair_le (ι : Fin b ↪ Fin z) {i j : Fin b} (hij : i ≠ j)
    {β : Fin (a+z) →₀ ℕ} (hi : privateExponent a s ι i ≤ β)
    (hj : privateExponent a s ι j ≤ β) :
    privateExponent a s ι i + privateExponent a s ι j ≤ β := by
  have hne : Fin.natAdd a (ι i) ≠ Fin.natAdd a (ι j) := by
    intro h
    exact hij (ι.injective (Fin.natAdd_injective z a h))
  intro k
  by_cases hki : k = Fin.natAdd a (ι i)
  · subst k
    simpa [privateExponent,Finsupp.single_apply,hne,Ne.symm hne] using hi (Fin.natAdd a (ι i))
  · by_cases hkj : k = Fin.natAdd a (ι j)
    · subst k
      simpa [privateExponent,Finsupp.single_apply,hne,Ne.symm hne] using hj (Fin.natAdd a (ι j))
    · simp [privateExponent,Finsupp.single_apply,hki,hkj,Ne.symm hki,Ne.symm hkj]

/-- In degree twice the private exponent, an overlap determines the entire
monomial; no other factor can occur. -/
theorem private_pair_target (ι : Fin b ↪ Fin z) {i j : Fin b} (hij : i ≠ j)
    {β : Fin (a+z) →₀ ℕ} (hβ : β.degree = 2*s)
    (hi : privateExponent a s ι i ≤ β) (hj : privateExponent a s ι j ≤ β) :
    β = privateExponent a s ι i + privateExponent a s ι j := by
  apply (equal_of_le_equal_degree (private_pair_le ι hij hi hj) ?_).symm
  simp only [map_add,privateExponent_degree,hβ]
  omega

/-- Below twice the private exponent, there cannot be two distinct columns. -/
theorem privateDivisors_card_le_one (hs : 0 < s) (ι : Fin b ↪ Fin z)
    (β : Fin (a+z) →₀ ℕ) (hβ : β.degree < 2*s) :
    (privateDivisors (s := s) ι β).card ≤ 1 := by
  have hb := privateDivisors_degree_bound (s := s) ι β
  nlinarith

/-- At twice the private exponent there are at most two columns. -/
theorem privateDivisors_card_le_two_exact (hs : 0 < s) (ι : Fin b ↪ Fin z)
    (β : Fin (a+z) →₀ ℕ) (hβ : β.degree = 2*s) :
    (privateDivisors (s := s) ι β).card ≤ 2 := by
  have hb := privateDivisors_degree_bound (s := s) ι β
  rw [hβ] at hb
  nlinarith

/-- A second private divisor can appear in a column product only when the
coefficient itself is precisely that second private power. -/
theorem private_overlap_coefficient (ι : Fin b ↪ Fin z) {i j : Fin b} (hij : i ≠ j)
    {α : Fin (a+z) →₀ ℕ} (hα : α.degree = s)
    (hj : privateExponent a s ι j ≤ privateExponent a s ι i + α) :
    α = privateExponent a s ι j := by
  have ht := private_pair_target ι hij
    (β := privateExponent a s ι i + α)
    (by simp only [map_add,privateExponent_degree,hα]; omega)
    (le_add_right le_rfl) hj
  exact add_left_cancel ht

/-- The two-column overlap has exactly its two prescribed private divisors. -/
theorem private_pair_divisors (hs : 0 < s) (ι : Fin b ↪ Fin z) (i j k : Fin b) :
    privateExponent a s ι k ≤ privateExponent a s ι i + privateExponent a s ι j ↔
      k = i ∨ k = j := by
  constructor
  · intro hk
    by_cases hki : k = i
    · exact Or.inl hki
    · exact Or.inr ((privateExponent_injective hs ι)
        (private_overlap_coefficient ι (Ne.symm hki) (privateExponent_degree ι j) hk).symm)
  · rintro (rfl | rfl)
    · exact le_add_right le_rfl
    · exact le_add_left le_rfl

end Froberg.PrivateColumns
