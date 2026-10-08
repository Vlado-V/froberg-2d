import Froberg.ProfileProbabilities
import Froberg.ProfileTotalLimits

/-! The outer target/source dimension ratio has the same critical leading
coefficient as the number of degree-d generators. -/
noncomputable section
namespace Froberg

lemma profile_capacity_factorials (s : ℕ) :
    profileAmbientCapacity s * (s.factorial : ℝ) * ((s+1).factorial : ℝ) =
      ((2*s+1).factorial : ℝ) := by
  have h := Nat.choose_mul_factorial_mul_factorial (show s ≤ 2*s+1 by omega)
  rw [show 2*s+1-s=s+1 by omega] at h
  exact_mod_cast h

lemma profile_scale_ratio (σ : ℝ) (s : ℕ) :
    targetProfileScale σ s / sourceProfileScale (profileAmbientCapacity s) σ s =
      (1-σ^s) / (((s+1).factorial : ℝ) * (profileAmbientCapacity s-σ^s)) := by
  have hH := profileAmbientCapacity_pos s
  have hfac (t : ℕ) : (t.factorial : ℝ) ≠ 0 := by positivity
  unfold targetProfileScale sourceProfileScale
  change profileAmbientCapacity s * (1-σ^s) / ((2*s+1).factorial : ℝ) /
    ((profileAmbientCapacity s-σ^s)/(s.factorial : ℝ)) = _
  rw [← profile_capacity_factorials s]
  field_simp
  <;> ring

lemma critical_profile_scale_ratio {σ ρ : ℝ} {s : ℕ}
    (hHρ : profileAmbientCapacity s * ρ * (2-ρ) = 1)
    (hσ : σ^s = profileAmbientCapacity s * ρ) (hρ : ρ < 1) :
    targetProfileScale σ s / sourceProfileScale (profileAmbientCapacity s) σ s =
      ρ / ((s+1).factorial : ℝ) := by
  have hH := profileAmbientCapacity_pos s
  have hden : profileAmbientCapacity s - σ^s ≠ 0 := by rw [hσ]; nlinarith
  have hfac : ((s+1).factorial : ℝ) ≠ 0 := by positivity
  rw [profile_scale_ratio]
  field_simp
  nlinarith [hσ]

lemma profileAmbientCapacity_eq_central (s : ℕ) :
    profileAmbientCapacity s = (centralHalfBinomial (s+1) : ℝ) := by
  unfold profileAmbientCapacity centralHalfBinomial
  congr 2 <;> omega

lemma limiting_profile_scale_ratio {d : ℕ} (hd : 3 ≤ d) :
    targetProfileScale (limitingCoreFraction d) (d-1) /
      sourceProfileScale (centralHalfBinomial d) (limitingCoreFraction d) (d-1) =
      criticalRatio d / (d.factorial : ℝ) := by
  have heq : d-1+1=d := by omega
  have hH : profileAmbientCapacity (d-1) = (centralHalfBinomial d : ℝ) := by
    rw [profileAmbientCapacity_eq_central, heq]
  have h := critical_profile_scale_ratio
    (s := d-1) (σ := limitingCoreFraction d) (ρ := criticalRatio d)
    (by rw [hH]; exact criticalRatio_identity (by omega))
    (by rw [hH]; exact limitingCoreFraction_pow hd)
    (criticalRatio_bounds (by omega)).2.1
  rwa [hH,heq] at h

end Froberg
