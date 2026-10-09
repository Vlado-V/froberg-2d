module

public import Quartic.UniformScalar.Counts

@[expose] public section

/-! The extra marked quadratic fits at both actual transfer endpoints. -/

namespace Quartic.MarkedEndpointBudget

open Counts UniformEndpoint UniformScalar

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem finite_table : ∀ i : Fin 292, ∀ upper : Bool,
    let m := (i : ℕ) + 28
    let c := FiniteCounts.mixedCount m upper
    c < m ∧ (FiniteCounts.upperEndpoint m : ℤ) +
      FiniteCounts.quadratics c + 4 ≤ FiniteCounts.quadratics m := by
  decide

private theorem product_margin_four {m q c : ℝ} (h : ValidCounts m q c) :
    4 ≤ alphaR m q - c * (c + 1) / 2 := by
  have hc := h.c_coarse
  have hq := h.q_coarse.2
  have hm0 : 0 ≤ m := by linarith [h.1]
  have hsq : 320 * m ≤ m ^ 2 := by nlinarith [h.1]
  have hcsq := mul_nonneg (sub_nonneg.mpr hc.2.2.1)
    (show 0 ≤ 3 * m / 5 + c by linarith [hc.2.1])
  unfold alphaR
  nlinarith [h.1]

/-- The marked square is a fourth extra column, uniformly for both endpoints. -/
theorem block_budgets (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    mixedCount m upper < m ∧
      upperEndpoint m + (mixedCount m upper + 1).choose 2 + 4 ≤
        (m + 1).choose 2 := by
  by_cases hsmall : m ≤ 319
  · have hf := finite_table ⟨m - 28, by omega⟩ upper
    have hm' : m - 28 + 28 = m := by omega
    simp only [hm'] at hf
    rw [upperEndpoint_eq_table m (by omega), mixedCount_eq_table m hsmall upper]
    refine ⟨hf.1, ?_⟩
    have hb := hf.2
    simp only [FiniteCounts.quadratics_eq_b2, b2] at hb
    exact_mod_cast hb
  · have h := actual_validCounts m (by omega) upper
    have hc := h.c_coarse
    have hclt : (mixedCount m upper : ℝ) < (m : ℝ) := by
      linarith [h.1, hc.2.2.1]
    refine ⟨by exact_mod_cast hclt, ?_⟩
    have hprod : (4 : ℝ) ≤ (alpha m (upperEndpoint m) : ℝ) -
        (b2 (mixedCount m upper) : ℝ) := by
      rw [alpha_cast, b2_cast]
      exact product_margin_four h
    have hprodi : 4 ≤ alpha m (upperEndpoint m) - b2 (mixedCount m upper) := by
      exact_mod_cast hprod
    simp only [alpha, b2] at hprodi
    omega

end Quartic.MarkedEndpointBudget
