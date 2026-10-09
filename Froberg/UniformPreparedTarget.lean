module

public import Froberg.PreparedTargetCore
public import Froberg.UniformLowRows
public import Froberg.UniformMiddleTargets

@[expose] public section

/-! A literal prepared-family target witness over every infinite field,
with the output and scalar thresholds fixed before choosing the field. -/
noncomputable section
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial Filter
open scoped Topology
attribute [local instance] tensorGroup

theorem eventually_prepared_target_witness_uniform {d : ℕ} (hd : 3≤d) (N₂ : ℕ)
    (hquad : ∀ h, N₂ ≤ h → ∀ (K : Type) [Field K] [Infinite K],
      GenericEndpoint K h 2 (upperCount h 2)) :
    ∀ᶠ h : ℕ in atTop, ∀ F : ℕ → ℕ,
      Tendsto (fun m : ℕ => (F m : ℝ)/(m : ℝ)^(d-1)) atTop
        (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))) →
      ∀ᶠ m : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K], ∀ r : ℕ,
        countAlpha d*(h : ℝ)^2*(m : ℝ)^(d-2)≤(r : ℝ) →
        ∃ D : MvPolynomial (Fin (finrank K (Fin (quadraticOutputDimension d h) → Forms K h 2))) K,
          (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 →
            LinearIndependent K ((Module.finBasis K (Fin (quadraticOutputDimension d h) → Forms K h 2)).equivFun.symm a) ∧
            ∀ (u q : ℕ) (S : Submodule K (Poly K h)) (hS : S≤Forms K h d)
              (u₀ : Fin u → S),Submodule.span K (Set.range u₀)=⊤ →
              S*Forms K h 1=Forms K h (d+1) → (¬Odd d → S=Forms K h d) →
              ∀ P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K,
                (∀ i,(P i).IsHomogeneous d) →
                (∀ i k,d≤k → coreComponent h m k (rename finSumFinEquiv (P i))=0) →
                HasUpperWitness d (F m) r q ((Module.finBasis K _).equivFun.symm a)
                  (fun i => homogeneousInclusion S hS (u₀ i)) P := by
  obtain ⟨layer,hcover,hMiddle⟩ := eventually_middle_rows_common_open_uniform hd
  filter_upwards [eventually_low_rows_shared_frames_uniform hd N₂ hquad,hMiddle] with h hLow hMiddle
  intro F hF
  filter_upwards [hLow F hF,hMiddle] with m hLow hMiddle
  intro K _ _ r hr
  obtain ⟨D,hD,hFrame⟩ := hLow K r hr
  obtain ⟨B,⟨g,hg⟩,hG⟩ := hMiddle K
  refine ⟨D,hD,?_⟩
  intro a ha
  obtain ⟨hLI,C,⟨c,hc⟩,hC⟩ := hFrame a ha
  refine ⟨hLI,?_⟩
  intro u q S hS u₀ hu₀ hcut heven P hPdeg hPlow
  exact exists_prepared_target_witness hd _ _ (hC c hc) layer hcover
    _ (hG g hg) S hS u₀ hu₀ hcut heven P hPdeg hPlow

end Froberg.PreparedTarget
