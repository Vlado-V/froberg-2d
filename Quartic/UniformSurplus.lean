module

public import Quartic.UniformSurplus.Rational

@[expose] public section

/-!
# Uniform scalar inequalities for every actual endpoint and every sharp profile

The uniform surplus is proved from the 32 Bernstein certificates by exact
interpolation and endpoint chords. The source real expression agrees with the
rational sharp expression used by the finite certificates. The final result
applies the scalar incidence theorem, with no numerical surplus hypothesis.

A geometric application must still establish that an actual subspace has an
ordered profile whose image dimension is bounded below by this expression.
-/

namespace Quartic.UniformSurplus
open Quartic.Counts Quartic.UniformEndpoint Quartic.UniformScalar
noncomputable section

/-- Both incidence inequalities for every nontrivial real ordered sharp profile
at the actual endpoint counts, for every child dimension at least 320. -/
theorem source_scalar_inequalities (m : ℕ) (hm : 320 ≤ m) (upper : Bool)
    (i : ℕ) (hi : i ≤ ProfileCertificate.coreA (mixedCount m upper))
    (n₁ n₂ n₃ : ℝ)
    (hn : 0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (ProfileCertificate.freeW m (mixedCount m upper):ℝ))
    (hdlo : 0 < (i:ℝ)+n₁+n₂+n₃)
    (hdhi : (i:ℝ)+n₁+n₂+n₃ < (ProfileCertificate.totalA m (mixedCount m upper):ℝ)) :
    let q := upperEndpoint m
    let c := mixedCount m upper
    let a : ℝ := ProfileCertificate.totalA m c
    let d := (i:ℝ)+n₁+n₂+n₃
    let E := sourceSharp m c i n₁ n₂ n₃
    let J : ℝ := j m q c
    let K : ℝ := k31 m c
    let S : ℝ := (H m q c:ℝ)+3+(delta m q:ℝ)
    d*((q:ℝ)+a-d) ≤ E ∧
      (covectorR J E q a d < 0 ∨
        covectorR J E q a d-codimensionR K S c d ≤ max (J-(hTotal m q c:ℝ)) 0-1) :=
  scalar_incidence_from_uniform_surplus m hm upper _ _ hdlo hdhi
    (source_uniform_surplus m hm upper i hi n₁ n₂ n₃ hn)

/-- A future geometric image bound can be inserted here directly. The theorem
requires only that the supplied image dimension dominate the already proved
sharp profile expression. -/
theorem scalar_inequalities_of_profile_bound (m : ℕ) (hm : 320 ≤ m) (upper : Bool)
    (i : ℕ) (hi : i ≤ ProfileCertificate.coreA (mixedCount m upper))
    (n₁ n₂ n₃ E : ℝ)
    (hn : 0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (ProfileCertificate.freeW m (mixedCount m upper):ℝ))
    (hdlo : 0 < (i:ℝ)+n₁+n₂+n₃)
    (hdhi : (i:ℝ)+n₁+n₂+n₃ < (ProfileCertificate.totalA m (mixedCount m upper):ℝ))
    (hE : sourceSharp m (mixedCount m upper) i n₁ n₂ n₃ ≤ E) :
    let q := upperEndpoint m
    let c := mixedCount m upper
    let a : ℝ := ProfileCertificate.totalA m c
    let d := (i:ℝ)+n₁+n₂+n₃
    let J : ℝ := j m q c
    let K : ℝ := k31 m c
    let S : ℝ := (H m q c:ℝ)+3+(delta m q:ℝ)
    d*((q:ℝ)+a-d) ≤ E ∧
      (covectorR J E q a d < 0 ∨
        covectorR J E q a d-codimensionR K S c d ≤ max (J-(hTotal m q c:ℝ)) 0-1) :=
  scalar_incidence_from_uniform_surplus m hm upper _ _ hdlo hdhi
    ((source_uniform_surplus m hm upper i hi n₁ n₂ n₃ hn).trans hE)

/-- The outer inequality includes both the empty and full profile, and hence
covers the manuscript's complete range `1≤d≤min(q,a)`. -/
theorem source_outer_inequality (m : ℕ) (hm : 320 ≤ m) (upper : Bool)
    (i : ℕ) (hi : i ≤ ProfileCertificate.coreA (mixedCount m upper))
    (n₁ n₂ n₃ : ℝ)
    (hn : 0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (ProfileCertificate.freeW m (mixedCount m upper):ℝ)) :
    let c := mixedCount m upper
    let d := (i:ℝ)+n₁+n₂+n₃
    d*((upperEndpoint m:ℝ)+(ProfileCertificate.totalA m c:ℝ)-d) ≤
      sourceSharp m c i n₁ n₂ n₃ := by
  have hdom := actual_domination m hm upper
  have hsign := structural_dimension_signs m hm upper
  have hJ : (0:ℝ) ≤ (j m (upperEndpoint m) (mixedCount m upper):ℝ) := by
    exact_mod_cast hsign.1.le
  have hTa : (targetCount m (mixedCount m upper):ℝ)/
      (ProfileCertificate.totalA m (mixedCount m upper):ℝ)=
      (upperEndpoint m:ℝ)+(j m (upperEndpoint m) (mixedCount m upper):ℝ)/
        (ProfileCertificate.totalA m (mixedCount m upper):ℝ) := by
    rw [target_count_identity m hm upper,add_div,mul_div_cancel_right₀ _ (ne_of_gt hdom.1)]
  have hE := source_uniform_surplus m hm upper i hi n₁ n₂ n₃ hn
  dsimp only at hE ⊢
  rw [hTa] at hE
  have hiR : (i:ℝ) ≤ (ProfileCertificate.coreA (mixedCount m upper):ℝ) := by exact_mod_cast hi
  have hdlo : 0 ≤ (i:ℝ)+n₁+n₂+n₃ := by
    have hi0 : (0:ℝ) ≤ i := by positivity
    linarith [hn.1,hn.2.1,hn.2.2.1]
  have hdhi : (i:ℝ)+n₁+n₂+n₃ ≤ (ProfileCertificate.totalA m (mixedCount m upper):ℝ) := by
    rw [source_total]
    linarith [hn.2.1,hn.2.2.1,hn.2.2.2]
  exact outer_of_uniform_surplus _ _ _ _ _ _ hdom.1 hJ hdom.2.2.2.2.2.le hdlo hdhi hE

end
end Quartic.UniformSurplus
