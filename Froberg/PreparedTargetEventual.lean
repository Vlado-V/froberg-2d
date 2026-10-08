import Froberg.PreparedTargetWitness
import Froberg.LowRowsExactOpen

/-! The prescribed counts admit one simultaneous literal prepared-family
witness, on a common nonempty open of quadratic output frames. -/
noncomputable section
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial Filter
open scoped Topology
variable {K : Type} [Field K] [CharZero K] {h m d H u : ℕ}
attribute [local instance] tensorGroup

def HasUpperWitness (d f r q : ℕ) (frame : Fin H → Forms K h 2)
    (U : Fin u → Forms K h d) (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K) : Prop :=
  ∃ p : Space m d q f u (activeEvenIndices d) (targetLayerCount d h m r) (targetLayerOutput frame),
    p.2.2=0 ∧ ∀ b,2≤b → b≤2*d → TargetLift
      ((Submodule.span K (Set.range (renamedGenerator U P p)))*Forms K (h+m) d) d b

theorem eventually_prepared_target_witness {d : ℕ} (hd : 3≤d) :
    ∀ᶠ h : ℕ in atTop, ∀ F : ℕ → ℕ,
      Tendsto (fun m : ℕ => (F m : ℝ)/(m : ℝ)^(d-1)) atTop
        (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))) →
      ∀ᶠ m : ℕ in atTop, ∀ r : ℕ,
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
  obtain ⟨layer,hcover,hMiddle⟩ := eventually_middle_rows_common_open (K := K) hd
  filter_upwards [eventually_low_rows_shared_frames (K := K) hd,hMiddle] with h hLow hMiddle
  intro F hF
  filter_upwards [hLow F hF,hMiddle] with m hLow hMiddle
  intro r hr
  obtain ⟨D,hD,hFrame⟩ := hLow r hr
  obtain ⟨B,⟨g,hg⟩,hG⟩ := hMiddle
  refine ⟨D,hD,?_⟩
  intro a ha
  obtain ⟨hLI,C,⟨c,hc⟩,hC⟩ := hFrame a ha
  refine ⟨hLI,?_⟩
  intro u q S hS u₀ hu₀ hcut heven P hPdeg hPlow
  exact exists_prepared_target_witness hd _ _ (hC c hc) layer hcover
    _ (hG g hg) S hS u₀ hu₀ hcut heven P hPdeg hPlow

end Froberg.PreparedTarget
