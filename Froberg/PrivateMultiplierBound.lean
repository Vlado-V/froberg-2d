module

public import Froberg.PrivateMultiplierCounts
public import Froberg.PrivateMultiplierLimits

@[expose] public section

/-! The actual good monomial set has more than the critical endpoint density. -/
noncomputable section
namespace Froberg.PrivateColumns
open Filter
open scoped Topology

theorem privateGoodMultipliers_lowerCount {a z s b : ℕ} (hs : 0<s)
    (ι : Fin b ↪ Fin z) :
    privateMultiplierLowerCount a z s b ≤ (privateGoodMultipliers a s ι).card := by
  have h := privateGoodMultipliers_card_lower (a := a) hs ι
  rw [show a+z+(s+1)-1=a+z+s by omega,
    show a+(s+1)-1=a+s by omega] at h
  unfold privateMultiplierLowerCount
  omega

theorem privateGoodMultipliers_eventually_above_critical {s : ℕ} (hs : 2 ≤ s)
    (b : ℕ) (a z : ℕ → ℕ) (hsplit : ∀ᶠ n : ℕ in atTop, a n+z n=n)
    (ha : Tendsto (fun n : ℕ => (a n : ℝ)/(n : ℝ)) atTop
      (𝓝 (limitingCoreFraction (s+1)))) :
    ∀ᶠ n : ℕ in atTop, ∀ ι : Fin b ↪ Fin (z n),
      criticalRatio (s+1)/((s+1).factorial : ℝ) <
        ((privateGoodMultipliers (a n) s ι).card : ℝ)/(n : ℝ)^(s+1) := by
  filter_upwards [private_multiplier_eventually_above_critical hs b a z hsplit ha] with n hn ι
  apply hn.trans_le
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast privateGoodMultipliers_lowerCount (a := a n) (by omega : 0<s) ι

end Froberg.PrivateColumns
