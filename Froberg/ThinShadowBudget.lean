module

public import Froberg.ScalarShadowBudgets

@[expose] public section

/-! The integer incidence budget in the thin, injective range. -/
noncomputable section
namespace Froberg.BilinearCovectorStrata

def thinSlices (j : ℕ) (C : ℝ) (r : ℕ) : ℕ := j-Nat.ceil (C*r)

lemma thinSlices_antitone (j : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    Antitone (thinSlices j C) := by
  intro r s hrs
  apply Nat.sub_le_sub_left
  apply Nat.ceil_mono
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hrs) hC

lemma thin_covector_budget {a r T q j E : ℕ} (ha : 0 < a) (hr : r ≤ a)
    (hT : T=q*a+j) (G C : ℝ) (hC : 0 ≤ C)
    (hG₁ : (a : ℝ)+C ≤ G) (hG₂ : (a : ℝ)+(j : ℝ)/a ≤ G)
    (hE : ((T : ℝ)/a)*r+G*(min r (a-r) : ℕ) ≤ E) :
    (r*(a-r) : ℕ)+(T : ℤ)-E-1 < (q*(a-r)+thinSlices j C r : ℕ) := by
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  have hrR : (r : ℝ) ≤ a := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hj0 : (0 : ℝ) ≤ (j : ℝ)/a := div_nonneg (Nat.cast_nonneg j) hap.le
  have hsub : ((a-r : ℕ) : ℝ)=(a : ℝ)-r := Nat.cast_sub hr
  have hratio : (T : ℝ)/a=(q : ℝ)+(j : ℝ)/a := by
    rw [hT]
    push_cast
    field_simp
  by_cases hl : r ≤ a-r
  · have hg : ((q*r+r*(a-r) : ℕ) : ℝ)+C*r ≤ E := by
      rw [min_eq_left hl,hratio] at hE
      have hm := mul_le_mul_of_nonneg_right hG₁ hr0
      have hj := mul_nonneg hj0 hr0
      push_cast
      rw [hsub]
      nlinarith [sq_nonneg (r : ℝ)]
    have hbase : q*r+r*(a-r) ≤ E := by
      have hc := mul_nonneg hC hr0
      exact_mod_cast (show ((q*r+r*(a-r) : ℕ) : ℝ) ≤ E by linarith)
    have hceil : Nat.ceil (C*r) ≤ E-(q*r+r*(a-r)) := by
      apply Nat.ceil_le.mpr
      rw [Nat.cast_sub hbase]
      linarith
    have hqa : q*a=q*r+q*(a-r) := by rw [← Nat.mul_add, Nat.add_sub_of_le hr]
    unfold thinSlices
    omega
  · have hh : a-r ≤ r := by omega
    have hg : q*r+r*(a-r)+j ≤ E := by
      rw [min_eq_right hh,hratio,hsub] at hE
      have hm := mul_le_mul_of_nonneg_right hG₂ (sub_nonneg.mpr hrR)
      have hj : ((j : ℝ)/a)*a=j := div_mul_cancel₀ _ (ne_of_gt hap)
      have hhR : (0 : ℝ) ≤ (a : ℝ)-r := sub_nonneg.mpr hrR
      have hb : ((q*r+r*(a-r)+j : ℕ) : ℝ) ≤ E := by
        push_cast
        rw [hsub]
        nlinarith [mul_nonneg hhR hhR]
      exact_mod_cast hb
    have hqa : q*a=q*r+q*(a-r) := by rw [← Nat.mul_add, Nat.add_sub_of_le hr]
    omega

end Froberg.BilinearCovectorStrata
