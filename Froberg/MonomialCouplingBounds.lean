import Froberg.FiniteMonomialTransport

/-! Uniform lower bounds for the individual divisor pairs in the lifted
monomial transport. -/
noncomputable section
namespace Froberg
open MonomialExpansion

lemma localMonomialCoupling_uniform_lower {a z s : ℕ} (ha : 0 < a) (hz : 0 < z)
    (i : Option (Fin s)) (j : Fin (2 * s + 1)) (hij : profileAllowed i j)
    (α : SourceMonomialFiber a z s i) (β : TargetMonomialFiber a z s j)
    (hdiv : OuterInjection.joinParts α.1.val α.2.val ≤ OuterInjection.joinParts β.1.val β.2.val) :
    1 / ((Fintype.card (TargetMonomialFiber a z s j) : ℝ) * 2 ^ (2 * s + 1)) ≤
      localMonomialCoupling i j α β := by
  have hfree : s - profileSourceIndex i ≤ 2 * s + 1 - j := by
    have hi := profileSourceIndex_le i
    rcases hij with ⟨h₁, h₂⟩
    omega
  have hab := (OuterInjection.joinParts_le_joinParts _ _ _ _).mp hdiv
  let A : ℝ := (a + j - 1).choose j
  let B : ℝ := (z + (2 * s + 1 - j) - 1).choose (2 * s + 1 - j)
  let C : ℝ := j.val.choose (profileSourceIndex i)
  let D : ℝ := (2 * s + 1 - j.val).choose (s - profileSourceIndex i)
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast Nat.choose_pos (show j.val ≤ a + j.val - 1 by omega)
  have hB : 0 < B := by
    dsimp [B]
    exact_mod_cast Nat.choose_pos (show 2 * s + 1 - j.val ≤ z + (2 * s + 1 - j.val) - 1 by omega)
  have hC : 0 < C := by
    dsimp [C]
    exact_mod_cast Nat.choose_pos hij.1
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast Nat.choose_pos hfree
  have hCD : C * D ≤ (2 : ℝ) ^ (2 * s + 1) := by
    have hnat := Nat.mul_le_mul (Nat.choose_le_two_pow j.val (profileSourceIndex i))
      (Nat.choose_le_two_pow (2 * s + 1 - j.val) (s - profileSourceIndex i))
    rw [← pow_add, Nat.add_sub_of_le (show j.val ≤ 2 * s + 1 by omega)] at hnat
    dsimp [C, D]
    exact_mod_cast hnat
  have hcard : (Fintype.card (TargetMonomialFiber a z s j) : ℝ) = A * B := by
    rw [targetMonomialFiber_card, Nat.cast_mul]
  have hden : (A * C) * (B * D) ≤ (A * B) * 2 ^ (2 * s + 1) := by
    have hh := mul_le_mul_of_nonneg_left hCD (mul_pos hA hB).le
    nlinarith
  have h₁ := divisibilityCoupling_lower ha hij.1 α.1 β.1 hab.1
  have h₂ := divisibilityCoupling_lower hz hfree α.2 β.2 hab.2
  change 1 / (A * C) ≤ divisibilityCoupling α.1 β.1 at h₁
  change 1 / (B * D) ≤ divisibilityCoupling α.2 β.2 at h₂
  rw [hcard]
  calc
    _ ≤ 1 / ((A * C) * (B * D)) :=
      one_div_le_one_div_of_le (mul_pos (mul_pos hA hC) (mul_pos hB hD)) hden
    _ = (1 / (A * C)) * (1 / (B * D)) := by ring
    _ ≤ localMonomialCoupling i j α β :=
      mul_le_mul h₁ h₂ (by positivity) (divisibilityCoupling_nonneg α.1 β.1)

/-- A joint lower bound and a target mass at most one give a uniform
conditional divisor bound, with the target-fiber cardinality canceled. -/
lemma conditional_lower_from_joint (N c ε q J : ℝ) (hN : 0 < N) (hc : 0 < c)
    (hε : 0 ≤ ε) (hq : 0 < q) (hq1 : q ≤ 1) (hJ : ε / (N * c) ≤ J) :
    ε / c ≤ J / (q / N) := by
  apply (le_div_iff₀ (div_pos hq hN)).mpr
  have hq' : (ε / (N * c)) * q ≤ ε / (N * c) :=
    mul_le_of_le_one_right (div_nonneg hε (mul_pos hN hc).le) hq1
  calc
    (ε / c) * (q / N) = (ε / (N * c)) * q := by ring
    _ ≤ ε / (N * c) := hq'
    _ ≤ J := hJ

end Froberg
