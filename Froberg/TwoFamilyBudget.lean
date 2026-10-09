module

public import Mathlib.Tactic

@[expose] public section

/-! The normalized two-family dimension ratio gives the full coefficient
incidence budget, including both Grassmannian overheads. -/
namespace Froberg

lemma two_family_weighted_budget {R₁ R₂ c₁ c₂ d₁ d₂ E : ℝ}
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hE : 0 ≤ E) (h₁ : R₁*d₁ ≤ E) (h₂ : R₂*d₂ ≤ E)
    (hratio : c₁/R₁+c₂/R₂ ≤ 1) : c₁*d₁+c₂*d₂ ≤ E := by
  have hd₁ : d₁ ≤ E/R₁ := (le_div_iff₀ hR₁).mpr (by simpa [mul_comm] using h₁)
  have hd₂ : d₂ ≤ E/R₂ := (le_div_iff₀ hR₂).mpr (by simpa [mul_comm] using h₂)
  calc
    c₁*d₁+c₂*d₂ ≤ c₁*(E/R₁)+c₂*(E/R₂) := add_le_add
      (mul_le_mul_of_nonneg_left hd₁ hc₁) (mul_le_mul_of_nonneg_left hd₂ hc₂)
    _ = E*(c₁/R₁+c₂/R₂) := by ring
    _ ≤ E*1 := mul_le_mul_of_nonneg_left hratio hE
    _ = E := mul_one E

/-- The explicit overhead q_i d_i+d_i(a_i-d_i) is paid by the normalized
shadow slopes whenever the sum of the two enlarged dimension ratios is ≤1. -/
theorem two_family_incidence_budget {a₁ a₂ q₁ q₂ d₁ d₂ E : ℕ}
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (h₁ : R₁*d₁ ≤ E) (h₂ : R₂*d₂ ≤ E)
    (hratio : ((q₁+a₁ : ℕ) : ℝ)/R₁+((q₂+a₂ : ℕ) : ℝ)/R₂ ≤ 1) :
    d₁*(a₁-d₁)+q₁*d₁+d₂*(a₂-d₂)+q₂*d₂ ≤ E := by
  have he := two_family_weighted_budget hR₁ hR₂
    (show (0 : ℝ) ≤ (q₁+a₁ : ℕ) by positivity)
    (show (0 : ℝ) ≤ (q₂+a₂ : ℕ) by positivity)
    (show (0 : ℝ) ≤ E by positivity) h₁ h₂ hratio
  have hn : (q₁+a₁)*d₁+(q₂+a₂)*d₂ ≤ E := by exact_mod_cast he
  have hl₁ := Nat.mul_le_mul_left d₁ (Nat.sub_le a₁ d₁)
  have hl₂ := Nat.mul_le_mul_left d₂ (Nat.sub_le a₂ d₂)
  nlinarith

end Froberg
