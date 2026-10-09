module

public import Froberg.CapacityRowGain
public import Froberg.JointConditionals
public import Froberg.NormalizedLimits

@[expose] public section

/-! Strict growth for a finite system of source and target capacities,
with its actual joint transport. -/
noncomputable section
namespace Froberg
open Finset
variable {I J : Type*} [Fintype I] [Fintype J]

lemma capacity_weighted_mean (d ell : I → ℝ) (A : ℝ) (hd : ∀ i, d i ≠ 0) :
    weightedMean (fun i => d i / A) (fun i => ell i / d i) = (∑ i, ell i) / A := by
  unfold weightedMean
  rw [sum_div]
  apply sum_congr rfl
  intro i _
  field_simp [hd i]

/-- A concrete capacity transport gives a strict shadow inequality.
The hypotheses only involve finite sums and pointwise inequalities. -/
theorem capacity_transport_growth (d ell : I → ℝ) (c b : J → ℝ)
    (P : I → J → ℝ) (q : I → ℝ) (A T η κ : ℝ)
    (hA : 0 < A) (hT : 0 < T) (hd : ∀ i, 0 < d i) (hc : ∀ j, 0 < c j)
    (hdsum : ∑ i, d i = A) (hcsum : ∑ j, c j = T)
    (hell : ∀ i, 0 ≤ ell i ∧ ell i ≤ d i)
    (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = d i / A)
    (hcol : ∀ j, ∑ i, P i j = c j / T)
    (hq : ∑ i, q i = 1) (hq0 : ∀ i, 0 ≤ q i)
    (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    (hcap : ∀ i j, 0 < P i j → c j ≤ d i)
    (hshadow : ∀ i j, 0 < P i j → min (c j) (ell i) ≤ b j)
    (hminor : ∀ i k, κ * (d i / A) * q k ≤
      reversibleWeights (fun j => c j / T) (jointConditional P (fun j => c j / T)) i k)
    (hdecrease : ∀ i, η * (d i / A) ≤
      ∑ j, P i j * (min (c j) (d i - c j) / c j)) :
    (T / A) * (∑ i, ell i) + (min η (κ/2) / 4) * (T / A) *
      min (∑ i, ell i) (A - ∑ i, ell i) ≤ ∑ j, b j := by
  let p := fun i => d i / A
  let ν := fun j => c j / T
  let C := jointConditional P ν
  let u := fun i => ell i / d i
  let D := fun j i => C j i * (min (c j) (d i - c j) / c j)
  let g := fun j => b j / c j
  have hν (j : J) : 0 < ν j := div_pos (hc j) hT
  have hC0 (j : J) (i : I) : 0 ≤ C j i := jointConditional_nonneg P ν hP (fun j => (hν j).le) j i
  have hC (j : J) : ∑ i, C j i = 1 := jointConditional_row P ν hcol (fun j => (hν j).ne') j
  have hp : ∑ i, p i = 1 := by dsimp [p]; rw [← sum_div, hdsum, div_self hA.ne']
  have hp0 (i : I) : 0 ≤ p i := (div_pos (hd i) hA).le
  have hu0 (i : I) : 0 ≤ u i := div_nonneg (hell i).1 (hd i).le
  have hu1 (i : I) : u i ≤ 1 := (div_le_one (hd i)).mpr (hell i).2
  have hmarginal (i : I) : ∑ j, ν j * C j i = p i :=
    jointConditional_source P ν p hrow (fun j => (hν j).ne') i
  have hpos (j : J) (i : I) (h : 0 < C j i) : 0 < P i j :=
    (div_pos_iff_of_pos_right (hν j)).mp h
  have hr (j : J) := capacity_row_gain (C j) d u (c j) (g j) (hC0 j) (hC j) (hc j)
    (fun i hi => hcap i j (hpos j i hi)) hu0 hu1 (fun i hi => by
      have h₁ : d i * u i = ell i := by dsimp [u]; field_simp [(hd i).ne']
      have h₂ : c j * g j = b j := by dsimp [g]; field_simp [(hc j).ne']
      rw [h₁, h₂]
      exact hshadow i j (hpos j i hi))
  have hdec (i : I) : η * p i ≤ ∑ j, ν j * D j i := by
    simpa only [D, C, p, ← mul_assoc, jointConditional_joint P ν (fun j => (hν j).ne')] using hdecrease i
  have hg := strict_transport_gain ν C D p q u g η κ (fun j => (hν j).le) hC0 hC hp hp0 hq hq0
    hmarginal hu0 hu1 hη hκ hminor (fun j => (hr j).1) (fun j => (hr j).2) hdec
  have hmean : weightedMean p u = (∑ i, ell i) / A := capacity_weighted_mean d ell A (fun i => (hd i).ne')
  have htarget : (∑ j, ν j * g j) = (∑ j, b j) / T := capacity_weighted_mean c b T (fun j => (hc j).ne')
  have hmb := weightedMean_bounds p u hp hp0 hu0 hu1
  have hquad := quadratic_defect_ge_half_min (weightedMean p u) hmb.1 hmb.2
  have hcoef : 0 ≤ min η (κ/2) / 2 := by positivity
  have hsmall := mul_le_mul_of_nonneg_left hquad hcoef
  have hstrict : weightedMean p u + (min η (κ/2) / 4) *
      min (weightedMean p u) (1 - weightedMean p u) ≤ ∑ j, ν j * g j := by
    nlinarith
  rw [hmean, htarget] at hstrict
  have hcomp : 1 - (∑ i, ell i) / A = (A - ∑ i, ell i) / A := by field_simp
  rw [hcomp, min_div_div_right hA.le] at hstrict
  have hh := mul_le_mul_of_nonneg_left hstrict hT.le
  have heq : T * ((∑ i, ell i) / A + min η (κ/2) / 4 *
      (min (∑ i, ell i) (A-∑ i, ell i) / A)) =
      (T/A) * (∑ i, ell i) + (min η (κ/2) / 4) * (T/A) *
        min (∑ i, ell i) (A-∑ i, ell i) := by ring
  simpa only [heq, mul_div_cancel₀ _ hT.ne'] using hh

end Froberg
