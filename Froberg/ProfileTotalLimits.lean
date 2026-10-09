module

public import Froberg.FiniteProfileTransport

@[expose] public section

/-! Leading terms of the exact source and coarse target dimensions. -/
noncomputable section
namespace Froberg
open Finset Filter
open scoped Topology

theorem sourceProfile_total_limit {H σ : ℝ} {s : ℕ}
    (hH : 1 < H) (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s)
    (a b : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 σ))
    (hbr : Tendsto (fun n : ℕ => (b n : ℝ) / n) atTop (𝓝 (1 - σ))) :
    Tendsto (fun n => (∑ i, finiteSourceProfile H s (a n) (b n) i) / (n : ℝ)^s)
      atTop (𝓝 (sourceProfileScale H σ s)) := by
  have hi (i : Option (Fin s)) : profileSourceIndex i ≤ s := by
    cases i <;> simp only [profileSourceIndex] <;> omega
  have hw (i : Option (Fin s)) := finiteProfileWeight_limit a b σ
    (profileSourceCapacity H i) s (profileSourceIndex i) (hi i) ha hb har hbr
  have hh := tendsto_finsetSum univ (fun i _ => hw i)
  simp only [raw_sourceProfileWeight hH hσ hσ1 hs, ← mul_sum,
    profileSourceMass_sum hH hσ hσ1 hs, mul_one, ← sum_div] at hh
  exact hh

theorem targetProfile_total_limit {σ : ℝ} {s : ℕ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s)
    (a b : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 σ))
    (hbr : Tendsto (fun n : ℕ => (b n : ℝ) / n) atTop (𝓝 (1 - σ))) :
    Tendsto (fun n => (∑ j, finiteTargetProfile s (a n) (b n) j) / (n : ℝ)^(2*s+1))
      atTop (𝓝 (targetProfileScale σ s)) := by
  have hw (j : Fin (2*s+1)) := finiteProfileWeight_limit a b σ
    (profileTargetCapacity s j) (2*s+1) j (by omega) ha hb har hbr
  have hh := tendsto_finsetSum univ (fun j _ => hw j)
  simp only [raw_targetProfileWeight hσ hσ1 hs, ← mul_sum,
    profileTargetMass_sum hσ hσ1 hs, mul_one, ← sum_div] at hh
  exact hh

theorem target_source_ratio_limit {H σ : ℝ} {s : ℕ}
    (hH : 1 < H) (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s)
    (a b : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 σ))
    (hbr : Tendsto (fun n : ℕ => (b n : ℝ) / n) atTop (𝓝 (1 - σ))) :
    Tendsto (fun n => ((∑ j, finiteTargetProfile s (a n) (b n) j) /
      (∑ i, finiteSourceProfile H s (a n) (b n) i)) / (n : ℝ)^(s+1))
      atTop (𝓝 (targetProfileScale σ s / sourceProfileScale H σ s)) := by
  have hh := (targetProfile_total_limit hσ hσ1 hs a b ha hb har hbr).div
    (sourceProfile_total_limit hH hσ hσ1 hs a b ha hb har hbr)
    (sourceProfileScale_pos hH hσ hσ1 hs).ne'
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp : (n : ℝ)^(2*s+1) = (n : ℝ)^s * (n : ℝ)^(s+1) := by
    rw [← pow_add]
    congr 1
    omega
  dsimp only [Pi.div_apply]
  rw [hp]
  field_simp

/-- Normalization used in the common-target mixing coefficient. -/
def monomialMixingCoefficient (s a b : ℕ) (H ε : ℝ) : ℝ :=
  (b : ℝ) * ε^2 * ((b+s-1).choose s : ℝ) *
    (∑ i, finiteSourceProfile H s a b i) /
    (((a+b+(2*s+1)-1).choose (2*s+1) : ℝ) * (2^(2*s+1))^2 * H)

theorem monomialMixingCoefficient_limit {H σ : ℝ} {s : ℕ}
    (hH : 1 < H) (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s)
    (a b : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 σ))
    (hbr : Tendsto (fun n : ℕ => (b n : ℝ) / n) atTop (𝓝 (1 - σ)))
    (hab : ∀ n, a n + b n = n) (ε : ℝ) :
    Tendsto (fun n => monomialMixingCoefficient s (a n) (b n) H ε) atTop
      (𝓝 ((1-σ) * ε^2 * ((1-σ)^s / (s.factorial : ℝ)) * sourceProfileScale H σ s /
        ((1 / ((2*s+1).factorial : ℝ)) * (2^(2*s+1))^2 * H))) := by
  have hB := scaled_index_monomial_limit b (1-σ) s hb hbr
  have hA := sourceProfile_total_limit hH hσ hσ1 hs a b ha hb har hbr
  have hN := scaled_index_monomial_limit (fun n : ℕ => n) 1 (2*s+1)
    tendsto_id (by simpa using scaled_power_normalized_limit (1 : ℝ) 1)
  simp only [one_pow] at hN
  have hden : (1 / ((2*s+1).factorial : ℝ)) * (2^(2*s+1))^2 * H ≠ 0 := by
    have : 0 < H := by linarith
    positivity
  have hh := (((hbr.mul_const (ε^2)).mul hB).mul hA).div
    ((hN.mul_const (((2 : ℝ)^(2*s+1))^2)).mul_const H) hden
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp only [Pi.div_apply]
  unfold monomialMixingCoefficient
  rw [hab n]
  have hp : (n : ℝ)^(2*s+1) = (n : ℝ) * (n : ℝ)^s * (n : ℝ)^s := by
    calc
      (n : ℝ)^(2*s+1) = (n : ℝ)^(1+s+s) := by congr 1; omega
      _ = (n : ℝ) * (n : ℝ)^s * (n : ℝ)^s := by rw [pow_add, pow_add, pow_one]
  rw [hp]
  field_simp
  <;> ring

theorem monomialMixingCoefficient_eventually_pos {H σ : ℝ} {s : ℕ}
    (hH : 1 < H) (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s)
    (a b : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 σ))
    (hbr : Tendsto (fun n : ℕ => (b n : ℝ) / n) atTop (𝓝 (1 - σ)))
    (hab : ∀ n, a n + b n = n) {ε : ℝ} (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ n in atTop, κ ≤ monomialMixingCoefficient s (a n) (b n) H ε := by
  have hh := monomialMixingCoefficient_limit hH hσ hσ1 hs a b ha hb har hbr hab ε
  have hS := sourceProfileScale_pos hH hσ hσ1 hs
  have hH0 : 0 < H := by linarith
  have hσ0 : 0 < 1-σ := by linarith
  have hlim : 0 < (1-σ) * ε^2 * ((1-σ)^s / (s.factorial : ℝ)) * sourceProfileScale H σ s /
        ((1 / ((2*s+1).factorial : ℝ)) * (2^(2*s+1))^2 * H) := by positivity
  exact ⟨_, half_pos hlim, (hh.eventually (lt_mem_nhds (half_lt_self hlim))).mono (fun _ h => h.le)⟩

end Froberg
