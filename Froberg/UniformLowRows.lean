module

public import Froberg.LowRowsCommonOpen
public import Froberg.UniformRowTwo
public import Froberg.UniformQuadraticTargets

@[expose] public section

/-! The three low target rows share one output frame and coefficient family.
Both variable thresholds precede the choice of infinite coefficient field. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace Froberg
open Module MvPolynomial Filter Quartic
open scoped Topology
universe u
attribute [local instance] tensorGroup

theorem eventually_low_rows_shared_frames_uniform {d : ℕ} (hd : 3≤d) (N₂ : ℕ)
    (hquad : ∀ h, N₂ ≤ h → ∀ (K : Type u) [Field K] [Infinite K],
      GenericEndpoint K h 2 (upperCount h 2)) :
    ∀ᶠ h : ℕ in atTop, ∀ F : ℕ → ℕ,
      Tendsto (fun m : ℕ => (F m : ℝ)/(m : ℝ)^(d-1)) atTop
        (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))) →
      ∀ᶠ m : ℕ in atTop, ∀ (K : Type u) [Field K] [Infinite K], ∀ rE : ℕ,
        countAlpha d*(h : ℝ)^2*(m : ℝ)^(d-2) ≤ (rE : ℝ) →
        ∃ D : MvPolynomial (Fin (finrank K (Fin (quadraticOutputDimension d h) → Forms K h 2))) K,
          (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 →
            LinearIndependent K ((Module.finBasis K (Fin (quadraticOutputDimension d h) → Forms K h 2)).equivFun.symm a) ∧
            ∃ E : MvPolynomial (Fin (finrank K
              (LowRowCoefficients K h m (d-1) (d-2) (quadraticOutputDimension d h) (F m) rE))) K,
              (∃ c,eval c E≠0) ∧ ∀ c,eval c E≠0 →
                LowRowsSurjective (by omega : (d-2)+d=(d-1)+(d-1))
                  ((Module.finBasis K _).equivFun.symm a) ((Module.finBasis K _).equivFun.symm c) := by
  obtain ⟨k,rfl⟩ : ∃ k,d=k+3 := ⟨d-3,by omega⟩
  filter_upwards [eventually_row_two_exact_uniform hd,
    eventually_quadratic_row_three_exact_uniform hd,
    eventually_quadratic_row_four_exact_of_endpoint_uniform hd N₂ hquad] with h h₂ h₃ h₄
  intro F hF
  filter_upwards [h₂ F hF,h₃,h₄] with m hm₂ hm₃ hm₄
  intro K _ _ rE hrE
  apply low_rows_shared_frame_open (by omega : ((k+3)-2)+(k+3)=((k+3)-1)+((k+3)-1))
  · have hrow := hm₂ K rE hrE
    unfold RowTwoTargetWitness at hrow
    obtain ⟨o,f,W,O,g,he,hW,hs⟩ := hrow
    exact ⟨o,f,W,O,g,hW,hs⟩
  · exact hm₃ K rE hrE
  · exact hm₄ K rE hrE

end Froberg
