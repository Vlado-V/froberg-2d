import Quartic.UniformScalar.EndpointBounds

/-! Real polynomial estimates for the infinite-range scalar counts. -/

namespace Quartic.UniformScalar

open Quartic.UniformEndpoint

noncomputable section

def alphaR (m q : ℝ) : ℝ := m * (m + 1) / 2 - q
def betaR (m q : ℝ) : ℝ := m * (m + 1) * (m + 2) / 6 - m*q
def jR (m q c : ℝ) : ℝ := 3 * betaR m q - c * alphaR m q
def HR (m q c : ℝ) : ℝ := 3*m*c - 2*alphaR m q - c*(c-1)/2
def aR (m c : ℝ) : ℝ := 3*m-c

/-- The already proved endpoint approximation and sharp mixed-count interval. -/
def ValidCounts (m q c : ℝ) : Prop :=
  320 ≤ m ∧ baseCount m ≤ q ∧ q ≤ baseCount m + 2 ∧
    6*rho*m-4 < c ∧ c < 6*rho*m-1/2

theorem actual_validCounts (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    ValidCounts m (upperEndpoint m) (mixedCount m upper) := by
  have hq := upper_endpoint_bounds m (by omega)
  have hc := mixed_count_bounds m hm upper
  exact ⟨by exact_mod_cast hm, hq.1, hq.2, hc.1, hc.2⟩

theorem ValidCounts.c_coarse {m q c : ℝ} (h : ValidCounts m q c) :
    m/2 < c ∧ 4 ≤ c ∧ c ≤ 3*m/5 ∧ c ≤ m := by
  have hm0 : 0 ≤ m := by linarith [h.1]
  have hr := rho_bounds
  have hlo := mul_nonneg (sub_nonneg.mpr hr.1) hm0
  have hhi := mul_nonneg (sub_nonneg.mpr hr.2) hm0
  rcases h with ⟨hm, _, _, hclo, hchi⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem ValidCounts.q_coarse {m q c : ℝ} (h : ValidCounts m q c) :
    0 ≤ q ∧ q ≤ m^2/10+m/2+2 := by
  have hm0 : 0 ≤ m := by linarith [h.1]
  have hr := rho_bounds
  have hlo := mul_nonneg (show 0 ≤ rho by linarith) (sq_nonneg m)
  have hhi := mul_nonneg (show 0 ≤ 1/10-rho by linarith) (sq_nonneg m)
  rcases h with ⟨_, hqlo, hqhi, _, _⟩
  unfold baseCount at hqlo hqhi
  constructor <;> nlinarith

theorem quadratic_room (m : ℝ) (hm : 320 ≤ m) :
    0 ≤ m*(m+1)/2-(baseCount m+2) := by
  have hprod := mul_nonneg (show 0 ≤ 1/10-rho by linarith [rho_bounds.2]) (sq_nonneg m)
  have hsq : 320*m ≤ m^2 := by nlinarith
  unfold baseCount
  nlinarith

/-- Cancellation of the cubic leading term at the endpoint approximation. -/
theorem jR_at_offsets (m e k : ℝ) :
    jR m (baseCount m+e) (6*rho*m+k) =
      -k*(1/2-rho)*m^2+(1-3*e+6*rho*e)*m+k*e := by
  unfold jR betaR alphaR baseCount
  linear_combination (m^3/2)*rho_identity

/-- Both polynomial bounds on `j` stated in the manuscript. -/
theorem ValidCounts.j_bounds {m q c : ℝ} (h : ValidCounts m q c) :
    (1/2-rho)*m^2/2+(12*rho-5)*m-1 ≤ jR m q c ∧
      jR m q c ≤ 4*(1/2-rho)*m^2+m := by
  have hc := h.c_coarse
  have hm0 : 0 ≤ m := by linarith [h.1]
  have ha : 0 ≤ 3*m-c := by linarith [hc.2.2.2]
  have hroom := quadratic_room m h.1
  have hp₁ := mul_nonneg (sub_nonneg.mpr h.2.2.1) ha
  have hp₂ := mul_nonneg (show 0 ≤ 6*rho*m-1/2-c by linarith [h.2.2.2.2]) hroom
  have hlowIdentity : jR m q c-jR m (baseCount m+2) (6*rho*m-1/2) =
      (baseCount m+2-q)*(3*m-c)+(6*rho*m-1/2-c)*(m*(m+1)/2-(baseCount m+2)) := by
    unfold jR betaR alphaR
    ring
  have hlowCorner : jR m (baseCount m+2) (6*rho*m-1/2) =
      (1/2-rho)*m^2/2+(12*rho-5)*m-1 := by
    have he := jR_at_offsets m 2 (-1/2)
    convert he using 1 <;> ring_nf
  have hroom₀ : 0 ≤ m*(m+1)/2-baseCount m := by linarith
  have hp₃ := mul_nonneg (sub_nonneg.mpr h.2.1) ha
  have hp₄ := mul_nonneg (show 0 ≤ c-(6*rho*m-4) by linarith [h.2.2.2.1]) hroom₀
  have huppIdentity : jR m (baseCount m) (6*rho*m-4)-jR m q c =
      (q-baseCount m)*(3*m-c)+(c-(6*rho*m-4))*(m*(m+1)/2-baseCount m) := by
    unfold jR betaR alphaR
    ring
  have huppCorner : jR m (baseCount m) (6*rho*m-4) = 4*(1/2-rho)*m^2+m := by
    have he := jR_at_offsets m 0 (-4)
    convert he using 1 <;> ring_nf
  constructor <;> linarith

theorem ValidCounts.j_pos {m q c : ℝ} (h : ValidCounts m q c) : 0 < jR m q c := by
  have hj := h.j_bounds.1
  have hm0 : 0 ≤ m := by linarith [h.1]
  have hsq : 320*m ≤ m^2 := by nlinarith [h.1]
  have hrlo := mul_nonneg (show 0 ≤ rho by linarith [rho_bounds.1]) hm0
  have hrhi := mul_nonneg (show 0 ≤ 1/10-rho by linarith [rho_bounds.2]) (sq_nonneg m)
  nlinarith [h.1]

theorem ValidCounts.H_pos {m q c : ℝ} (h : ValidCounts m q c) : 0 < HR m q c := by
  have hc := h.c_coarse
  have hq := h.q_coarse.1
  have hm0 : 0 ≤ m := by linarith [h.1]
  have hsq : 320*m ≤ m^2 := by nlinarith [h.1]
  have hmc := mul_nonneg hm0 (show 0 ≤ c-m/2 by linarith [hc.1])
  have hcsq := mul_nonneg (sub_nonneg.mpr hc.2.2.1) (show 0 ≤ 3*m/5+c by linarith [hc.2.1])
  unfold HR alphaR
  nlinarith [h.1]

theorem ValidCounts.product_margin {m q c : ℝ} (h : ValidCounts m q c) :
    3 ≤ alphaR m q-c*(c+1)/2 := by
  have hc := h.c_coarse
  have hq := h.q_coarse.2
  have hm0 : 0 ≤ m := by linarith [h.1]
  have hsq : 320*m ≤ m^2 := by nlinarith [h.1]
  have hcsq := mul_nonneg (sub_nonneg.mpr hc.2.2.1) (show 0 ≤ 3*m/5+c by linarith [hc.2.1])
  unfold alphaR
  nlinarith [h.1]

theorem ValidCounts.cubic_margin {m q c : ℝ} (h : ValidCounts m q c) : 0 < betaR m q := by
  have hm0 : 0 < m := by linarith [h.1]
  have hq := h.q_coarse.2
  have hprod := mul_nonneg hm0.le (sub_nonneg.mpr hq)
  have hcube : 0 < m*(m^2-25) := mul_pos hm0 (by nlinarith [h.1])
  unfold betaR
  nlinarith

theorem ValidCounts.a_bounds {m q c : ℝ} (h : ValidCounts m q c) :
    0 < aR m c ∧ (3-6*rho)*m ≤ aR m c ∧ aR m c < 5*m/2+4 := by
  have hc := h.c_coarse
  have hm0 : 0 ≤ m := by linarith [h.1]
  have hr := mul_nonneg (show 0 ≤ rho-1/12 by linarith [rho_bounds.1]) hm0
  unfold aR
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [h.1, h.2.2.2.1, h.2.2.2.2]

theorem ValidCounts.j_div_a {m q c : ℝ} (h : ValidCounts m q c) :
    0 ≤ jR m q c/aR m c ∧ jR m q c/aR m c ≤ 2*m/3+1 := by
  have ha := h.a_bounds
  have hj := h.j_bounds.2
  have hm0 : 0 ≤ m := by linarith [h.1]
  have hp := mul_nonneg (show 0 ≤ 2*m/3+1 by linarith) (sub_nonneg.mpr ha.2.1)
  have hr := mul_nonneg (show 0 ≤ 1/3-rho by linarith [rho_bounds.2]) hm0
  refine ⟨div_nonneg h.j_pos.le ha.1.le, (div_le_iff₀ ha.1).2 ?_⟩
  nlinarith only [hj, hp, hr]

/-- The two uniform domination inequalities, together with `D>a`. -/
theorem ValidCounts.domination {m q c : ℝ} (h : ValidCounts m q c) :
    c+4+aR m c-jR m q c/aR m c < m^2/100 ∧
      aR m c+jR m q c/aR m c < m^2/100 ∧ aR m c < m^2/100 := by
  have ha := h.a_bounds
  have hj := h.j_div_a
  have hsq : 320*m ≤ m^2 := by nlinarith [h.1]
  have hD₁ : 3*m+4 < m^2/100 := by nlinarith [h.1]
  have hD₂ : 19*m/6+5 < m^2/100 := by nlinarith [h.1]
  have hid : c+aR m c = 3*m := by unfold aR; ring
  refine ⟨?_, ?_, ?_⟩ <;> linarith

end
end Quartic.UniformScalar
