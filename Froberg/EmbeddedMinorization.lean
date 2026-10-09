module

public import Froberg.TransportVariance

@[expose] public section

/-! A uniform distribution on an embedded family of source states, and
conversion of a common-target lower bound to a mixing minorization. -/
noncomputable section
namespace Froberg
open Finset
variable {A I : Type*} [Fintype A] [Fintype I]

def embeddedUniform (e : A ↪ I) (i : I) : ℝ := by
  classical
  exact ∑ a, if e a = i then 1 / (Fintype.card A : ℝ) else 0

lemma embeddedUniform_nonneg (e : A ↪ I) (i : I) : 0 ≤ embeddedUniform e i := by
  unfold embeddedUniform
  apply sum_nonneg
  intro a _
  split_ifs <;> positivity

lemma embeddedUniform_sum [Nonempty A] (e : A ↪ I) : ∑ i, embeddedUniform e i = 1 := by
  classical
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [embeddedUniform]
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, ite_true, sum_const, card_univ, nsmul_eq_mul]
  field_simp

lemma embeddedUniform_at (e : A ↪ I) (a : A) :
    embeddedUniform e (e a) = 1 / (Fintype.card A : ℝ) := by
  classical
  simp [embeddedUniform, e.injective.eq_iff]

lemma embeddedUniform_off (e : A ↪ I) (i : I) (hi : i ∉ Set.range e) : embeddedUniform e i = 0 := by
  apply sum_eq_zero
  intro a _
  exact if_neg (fun h => hi ⟨a, h⟩)

lemma embedded_family_minorization [Nonempty A] (e : A ↪ I)
    (W : I → I → ℝ) (p : I → ℝ) (B M : ℝ) (hB : 0 ≤ B) (hM : 0 < M)
    (hW : ∀ i k, 0 ≤ W i k) (hp : ∀ i, p i ≤ M)
    (hfamily : ∀ i a, B ≤ W i (e a)) :
    ∀ i k, (B * Fintype.card A / M) * p i * embeddedUniform e k ≤ W i k := by
  classical
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  intro i k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hk
    rw [embeddedUniform_at]
    calc
      (B * Fintype.card A / M) * p i * (1 / (Fintype.card A : ℝ)) = B * (p i / M) := by
        field_simp
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left ((div_le_one hM).mpr (hp i)) hB
      _ ≤ W i (e a) := by simpa using hfamily i a
  · rw [embeddedUniform_off e k hk, mul_zero]
    exact hW i k

end Froberg
