import Froberg.GeneratorCounts

/-! Integer selection with prescribed lower and upper bounds on the number
of variables in the auxiliary block. -/
namespace Froberg

theorem monomial_count_mono_variables {a b t : ℕ} (hab : a ≤ b) :
    (a + t - 1).choose t ≤ (b + t - 1).choose t :=
  Nat.choose_le_choose t (by omega)

theorem exists_exact_generator_count_with_bounds (K R emin t lo hi : ℕ)
    (hK : 0 < K) (ht : 0 < t)
    (hlo : K * (lo + t - 1).choose t + emin ≤ R)
    (hhi : R < K * (hi + 1 + t - 1).choose t) :
    ∃ a f e : ℕ, lo ≤ a ∧ a ≤ hi ∧
      f = K * (a + t - 1).choose t ∧ f + e = R ∧ emin ≤ e ∧
      e < emin + K * (hi + 1 + (t - 1) - 1).choose (t - 1) := by
  obtain ⟨a, f, e, hf, htotal, hemin, hewidth⟩ :=
    exists_exact_generator_count K R emin t hK ht (by omega)
  have hahi : a ≤ hi := by
    by_contra hn
    have hm := Nat.mul_le_mul_left K
      (monomial_count_mono_variables (t := t) (show hi + 1 ≤ a by omega))
    omega
  have hloa : lo ≤ a := by
    by_contra hn
    have hm := Nat.mul_le_mul_left K
      (monomial_count_mono_variables (t := t) (show a + 1 ≤ lo by omega))
    rw [monomial_count_step a t ht, Nat.mul_add] at hm
    omega
  have hwidth := Nat.mul_le_mul_left K (monomial_count_mono_variables
    (t := t - 1) (show a + 1 ≤ hi + 1 by omega))
  exact ⟨a, f, e, hloa, hahi, hf, htotal, hemin, by omega⟩

end Froberg
