import Froberg.CoreLower
import Froberg.AuxiliaryCounts
import Froberg.BlockParameters

/-! Simultaneous exact counts and the positive dimension reserve, with
arbitrarily large fixed block size. Both adjacent critical counts use the
same block and the same eventual threshold. -/
noncomputable section
namespace Froberg
open Polynomial Filter
open scoped Topology

structure FixedBlockConditions (d K h : ℕ) : Prop where
  multiplicity_pos : 0 < K
  size_eq : h = K * centralHalfBinomial d
  size_pos : 0 < h
  divisible : 720720 ∣ K
  columns_le : outerColumnCount d h ≤ h
  columns_large : (2 : ℝ) ^ d * criticalRatio d * h < (outerColumnCount d h : ℝ)
  deletion_large : 2 * h - 1 ≤ deletedTargetCount d h
  deletion_small : 9 ≤ d → (deletedTargetCount d h : ℝ) < (h : ℝ) ^ 2 / 10000

structure ExactCountConditions (d K h lo n a f e : ℕ) (upper : Bool) : Prop where
  core_lower : lo ≤ a
  core_le : a ≤ n
  core_upper : a ≤ ⌊coreFraction (d - 1) * (n : ℝ)⌋₊
  core_positive : (n : ℝ) / 4 < a
  outer_eq : f = K * (a + (d - 1) - 1).choose (d - 1)
  total : upperCount n d + f + auxiliaryGeneratorCount d h n + e =
    adjacentCriticalCount upper (n + h) d
  quadratic_lower : countAlpha d * (h : ℝ) ^ 2 * (n : ℝ) ^ (d - 2) ≤ (e : ℝ)
  quadratic_upper : (e : ℝ) < countBeta d * (h : ℝ) ^ 2 * (n : ℝ) ^ (d - 2)

def dimensionReserve (d h n f : ℕ) : ℝ :=
  (h : ℝ) * ((n + (2 * d - 1) - 1).choose (2 * d - 1) : ℝ) -
    (f : ℝ) * ((n + d - 1).choose d : ℝ) -
    (upperCount n d : ℝ) *
      ((h : ℝ) * ((n + (d - 1) - 1).choose (d - 1) : ℝ) - f)

theorem exact_count_and_margin_parameters {d : ℕ} (hd : 3 ≤ d)
    (lo minBlock : ℕ) :
    ∃ K h : ℕ, minBlock ≤ h ∧ FixedBlockConditions d K h ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ upper : Bool,
        ∃ a f e : ℕ, ExactCountConditions d K h lo n a f e upper ∧
          δ * (n : ℝ) ^ (2 * d - 2) < dimensionReserve d h n f := by
  obtain ⟨P, hP, hlead, _, he⟩ := exists_critical_polynomial_approximation (by omega : 2 ≤ d)
  have hcoeff : P.coeff d = criticalRatio d / (d.factorial : ℝ) := by
    simpa only [hP, criticalRatio] using (coeff_natDegree (p := P)).trans hlead
  obtain ⟨S, hS⟩ := exact_count_positive_margin hd P hP.le hcoeff he
  obtain ⟨W, hW⟩ := count_width_eventually hd
  obtain ⟨B, hB⟩ := eventually_atTop.mp (block_parameters_eventually hd)
  let K := 720720 * (max minBlock (max W (max S B)) + 1)
  let h := K * centralHalfBinomial d
  have hK : 0 < K := by dsimp only [K]; omega
  have hbase : max minBlock (max W (max S B)) ≤ K := by dsimp only [K]; omega
  have hH : 1 ≤ centralHalfBinomial d := by
    have := centralHalfBinomial_ge_two (d := d) (by omega)
    omega
  have hKh : K ≤ h := by dsimp only [h]; nlinarith
  have hh : 0 < h := lt_of_lt_of_le hK hKh
  have hsize : h = K * centralHalfBinomial d := rfl
  have hwidth := hW K (by omega)
  obtain ⟨hl, hc, hs⟩ := hB h (by omega)
  obtain ⟨δ, hδ, hmargin⟩ := hS h (by omega) hh
  have hcounts (upper : Bool) := exact_critical_generator_counts_core hd hK hsize hwidth
    (auxiliaryGeneratorCount d h) (fun n => adjacentCriticalCount upper n d)
    (fun n _ => adjacentCriticalCount_bounds upper n d)
    (auxiliaryGeneratorCount_lower_order hd h) lo
  have hlow (upper : Bool) := exact_counts_core_positive hd hK hsize
    (auxiliaryGeneratorCount d h) (fun n => adjacentCriticalCount upper n d)
    (fun n _ => adjacentCriticalCount_bounds upper n d)
    (auxiliaryGeneratorCount_lower_order hd h)
  refine ⟨K, h, by omega, ⟨hK, hsize, hh, ?_, hl, outerColumnCount_strict_lower hd hh, hc, hs⟩, δ, hδ, ?_⟩
  · exact ⟨_, rfl⟩
  · filter_upwards [hcounts false, hcounts true, hlow false, hlow true, hmargin]
      with n hn₀ hn₁ hl₀ hl₁ hmn
    intro upper
    have hn : ∃ a f e : ℕ, lo ≤ a ∧ a ≤ n ∧
        a ≤ ⌊coreFraction (d - 1) * (n : ℝ)⌋₊ ∧
        f = K * (a + (d - 1) - 1).choose (d - 1) ∧
        upperCount n d + f + auxiliaryGeneratorCount d h n + e =
          adjacentCriticalCount upper (n + h) d ∧
        countAlpha d * (h : ℝ) ^ 2 * (n : ℝ) ^ (d - 2) ≤ (e : ℝ) ∧
        (e : ℝ) < countBeta d * (h : ℝ) ^ 2 * (n : ℝ) ^ (d - 2) := by
      cases upper <;> assumption
    obtain ⟨a, f, e, ha₀, ha₁, ha₂, hf, ht, he₀, he₁⟩ := hn
    have hapos : (n : ℝ) / 4 < a := by
      cases upper
      · exact hl₀ a f e hf ht he₁
      · exact hl₁ a f e hf ht he₁
    refine ⟨a, f, e, ⟨ha₀, ha₁, ha₂, hapos, hf, ht, he₀, he₁⟩, ?_⟩
    exact hmn _ f (auxiliaryGeneratorCount d h n) e
      (adjacentCriticalCount_bounds upper (n + h) d).1
      (adjacentCriticalCount_bounds upper (n + h) d).2 ht he₀

end Froberg
