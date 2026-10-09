module

public import Froberg.ProfileMarginals
public import Froberg.NormalizedLimits

@[expose] public section

/-! Raw source and coarse target profile weights, and their limiting
normalizations in the explicit transport. -/
noncomputable section
namespace Froberg
open Polynomial Finset Filter
open scoped Topology

def profileSourceCapacity (H : ℝ) {s : ℕ} : Option (Fin s) → ℝ
  | some _ => H
  | none => H - 1

def profileTargetCapacity (s : ℕ) (j : Fin (2 * s + 1)) : ℝ :=
  (((2 * s + 1).choose s : ℕ) : ℝ) - (j.val.choose s : ℝ)

def rawProfileWeight (c σ : ℝ) (r i : ℕ) : ℝ :=
  c * σ ^ i * (1 - σ) ^ (r - i) /
    ((i.factorial : ℝ) * ((r - i).factorial : ℝ))

def finiteProfileWeight (c : ℝ) (r i a b : ℕ) : ℝ :=
  c * ((a + i - 1).choose i : ℝ) * ((b + (r - i) - 1).choose (r - i) : ℝ)

def sourceProfileScale (H σ : ℝ) (s : ℕ) : ℝ := (H - σ ^ s) / (s.factorial : ℝ)
def targetProfileScale (σ : ℝ) (s : ℕ) : ℝ :=
  (((2 * s + 1).choose s : ℕ) : ℝ) * (1 - σ ^ s) / ((2 * s + 1).factorial : ℝ)

theorem profileBinomial_factorial (σ : ℝ) {r i : ℕ} (hi : i ≤ r) :
    profileBinomial σ r i = (r.factorial : ℝ) * σ ^ i * (1 - σ) ^ (r - i) /
      ((i.factorial : ℝ) * ((r - i).factorial : ℝ)) := by
  rw [profileBinomial, Nat.cast_choose ℝ hi]
  ring

theorem sourceProfileScale_pos {H σ : ℝ} {s : ℕ}
    (hH : 1 < H) (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s) :
    0 < sourceProfileScale H σ s := by
  have hp : σ ^ s < 1 := pow_lt_one₀ hσ.le hσ1 (by omega)
  exact div_pos (by linarith) (by positivity)

theorem targetProfileScale_pos {σ : ℝ} {s : ℕ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s) :
    0 < targetProfileScale σ s := by
  have hp : σ ^ s < 1 := pow_lt_one₀ hσ.le hσ1 (by omega)
  have hH : (0 : ℝ) < (2 * s + 1).choose s := by
    exact_mod_cast Nat.choose_pos (by omega : s ≤ 2 * s + 1)
  exact div_pos (mul_pos hH (by linarith)) (by positivity)

theorem raw_sourceProfileWeight {H σ : ℝ} {s : ℕ}
    (hH : 1 < H) (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s) (i : Option (Fin s)) :
    rawProfileWeight (profileSourceCapacity H i) σ s (profileSourceIndex i) =
      sourceProfileScale H σ s * profileSourceMass H σ s i := by
  have hp : σ ^ s < 1 := pow_lt_one₀ hσ.le hσ1 (by omega)
  have hden : H - σ ^ s ≠ 0 := by linarith
  have hfac (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  cases i with
  | none =>
      simp only [rawProfileWeight, profileSourceCapacity, profileSourceIndex, profileSourceMass,
        sourceProfileScale, Nat.sub_self, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one]
      field_simp
  | some i =>
      simp only [rawProfileWeight, profileSourceCapacity, profileSourceIndex, profileSourceMass,
        sourceProfileScale, profileBinomial_factorial σ (show i.val ≤ s by omega)]
      field_simp

theorem raw_targetProfileWeight {σ : ℝ} {s : ℕ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s) (j : Fin (2 * s + 1)) :
    rawProfileWeight (profileTargetCapacity s j) σ (2 * s + 1) j =
      targetProfileScale σ s * profileTargetMass σ s j := by
  have hp : σ ^ s < 1 := pow_lt_one₀ hσ.le hσ1 (by omega)
  have hden : 1 - σ ^ s ≠ 0 := by linarith
  have hH : ((((2 * s + 1).choose s : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : s ≤ 2 * s + 1)))
  have hfac (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [profileTargetMass_capacity, profileBinomial_factorial σ (show j.val ≤ 2 * s + 1 by omega)]
  unfold rawProfileWeight profileTargetCapacity targetProfileScale
  field_simp

theorem finiteProfileWeight_limit (a b : ℕ → ℕ) (σ c : ℝ) (r i : ℕ) (hi : i ≤ r)
    (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 σ))
    (hbr : Tendsto (fun n : ℕ => (b n : ℝ) / n) atTop (𝓝 (1 - σ))) :
    Tendsto (fun n : ℕ => finiteProfileWeight c r i (a n) (b n) / (n : ℝ) ^ r)
      atTop (𝓝 (rawProfileWeight c σ r i)) := by
  have hh := (split_monomial_profile_limit a b σ (1 - σ) r i hi ha hb har hbr).const_mul c
  have he : c * (σ ^ i * (1 - σ) ^ (r - i) /
      ((i.factorial : ℝ) * ((r - i).factorial : ℝ))) = rawProfileWeight c σ r i := by
    unfold rawProfileWeight
    ring
  rw [he] at hh
  apply hh.congr'
  exact Eventually.of_forall fun n => by
    dsimp only
    unfold finiteProfileWeight
    ring

end Froberg
