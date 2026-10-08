import Froberg.LeadingWitnessRename

/-! A paired-output construction yields independent leading layers on
the usual finite set of variables, for every sufficiently large block
size divisible by four. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
universe u
variable {K : Type} [Field K] [Infinite K]

theorem eventually_leading_witnesses_from_paired {d : ℕ} (hd : 3≤d)
    (hp : ∀ᶠ w : ℕ in atTop,4∣2*w → ∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ n : ℕ in atTop,
      ∀ (X : Type u) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) →
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) →
      (∀ R,4≤R → T R=0) →
      let A := Space n d (upperCount n d) (allEvenIndices d)
        (allEvenCount d (2*w) n (e n+extra)) (constrainedOutputs T)
      ∀ j : allEvenIndices d,∃ p : A,LinearIndependent K (p.2 j)) :
    ∀ᶠ h : ℕ in atTop,4∣h → ∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2)) →
      ∀ᶠ n : ℕ in atTop,
      ∀ (X : Type u) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → Poly K h →ₗ[K] X,
      finrank K X=deletedTargetCount d h →
      finrank K ↥(Forms K h 2⊓(T 2).ker)=quadraticOutputDimension d h →
      (∀ R,4≤R → T R=0) →
      let A := Space n d (upperCount n d) (allEvenIndices d)
        (allEvenCount d h n (e n+extra)) (fun j => Forms K h j⊓(T j).ker)
      ∀ j : allEvenIndices d,∃ p : A,LinearIndependent K (p.2 j) := by
  classical
  obtain ⟨W,hW⟩ := eventually_atTop.mp hp
  apply eventually_atTop.mpr
  refine ⟨2*W,?_⟩
  intro h hh hdiv extra e he
  let w := h/2
  have htwo : 2*w=h := Nat.mul_div_cancel' (dvd_trans (by decide : 2∣4) hdiv)
  have hw : W≤w := by dsimp [w]; omega
  have hdiv' : 4∣2*w := by simpa only [htwo] using hdiv
  have he' : ∀ᶠ n : ℕ in atTop,
      (e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2) := by
    have hcast : 2*(w : ℝ)=(h : ℝ) := by exact_mod_cast htwo
    simpa only [hcast] using he
  filter_upwards [hW w hw hdiv' extra e he'] with n hn
  intro X _ _ _ T hX hO hT
  let f : (Fin w × Bool) ≃ Fin h := Fintype.equivOfCardEq (by simp [←htwo,Nat.mul_comm])
  let T₀ := fun j => (T j).comp (rename f).toLinearMap
  have hX₀ : finrank K X=deletedTargetCount d (2*w) := by simpa only [htwo] using hX
  have hO₀ : finrank K (constrainedOutputs T₀ 2)=quadraticOutputDimension d (2*w) := by
    exact (homogeneous_kernel_rename_finrank f (T 2) 2).trans (by simpa only [htwo] using hO)
  have hT₀ : ∀ R,4≤R → T₀ R=0 := by
    intro R hR
    simp only [T₀,hT R hR,LinearMap.zero_comp]
  have H := leading_witnesses_constraint_rename T f (hn X T₀ hX₀ hO₀ hT₀)
  have hcounts : allEvenCount d (2*w) n (e n+extra)=allEvenCount d h n (e n+extra) := by
    rw [htwo]
  exact (leading_witnesses_congr_counts (fun j => Forms K h j⊓(T j).ker) hcounts).mp H

end Froberg.PreparedParameters
