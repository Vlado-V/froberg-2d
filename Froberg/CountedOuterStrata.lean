module

public import Froberg.OuterPositiveDeficit
public import Froberg.ThinModelLimits
public import Froberg.CountedPrivateOpen

@[expose] public section

/-! The thin covector statement for exactly the outer counts in the manuscript. -/
noncomputable section
namespace Froberg.VectorExpansionOpen
open Filter Module MvPolynomial Quartic VectorMultiplicationCoordinates
open BilinearScalarFamily
open scoped Topology
variable {K : Type*} [Field K] [Infinite K] {d h b : ℕ}

def outerScalarDeficit {c : ℕ} (g : Fin c → Rows K h n (d-1)) : ℕ :=
  finrank K (Target g d)-upperCount n d*finrank K (Source g)

theorem eventually_counted_outer_strata (hd : 3 ≤ d) (hh : 0 < h)
    (f : ℕ → ℕ) (G : ℝ) (hG : 0 < G) {δ : ℝ} (hδ : 0 < δ)
    (hf : Tendsto (fun n : ℕ => (f n : ℝ)/(n : ℝ)^(d-1)) atTop
      (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))))
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ n in atTop,
      ∀ g : Fin (f n+b) → Rows K h n (d-1),StrictModel g d (G*(n : ℝ)^d) →
        HasThinQuotientOpen (quotientMultiplication g d) (upperCount n d)
          (outerScalarDeficit g) (C*(n : ℝ)^d) := by
  obtain ⟨hA,hJ⟩ := outer_count_limits (b := b) hd f hf
  have hpos := outer_deficit_eventually_positive (b := b) hd f hδ hreserve
  have hbudget := thin_shadow_eventual_budget (outerSourceCount d h b f)
    (fun n => outerTargetCount d h b f n-(upperCount n d : ℝ)*outerSourceCount d h b f n)
    (d-1) _ G (outer_source_leading_pos (by omega) hh) hG hA
    (by simpa only [show 2*(d-1)+1=2*d-1 by omega] using hJ)
  refine ⟨G/2,by positivity,?_⟩
  filter_upwards [hpos,hbudget,eventually_gt_atTop (0 : ℕ)] with n hj hb hn
  intro g hg
  have hs : (finrank K (Source g) : ℝ)=outerSourceCount d h b f n := by
    rw [hg.source_real_count hn]
    unfold outerSourceCount
    push_cast
    ring
  have ht : (finrank K (Target g d) : ℝ)=outerTargetCount d h b f n := by
    rw [hg.target_real_count hn,show d-1+d=2*d-1 by omega]
    unfold outerTargetCount
    push_cast
    rfl
  have hle : upperCount n d*finrank K (Source g) ≤ finrank K (Target g d) := by
    have hr : (upperCount n d : ℝ)*finrank K (Source g) ≤ finrank K (Target g d) := by
      rw [hs,ht]
      linarith
    exact_mod_cast hr
  have hjcast : (outerScalarDeficit g : ℝ)=
      outerTargetCount d h b f n-(upperCount n d : ℝ)*outerSourceCount d h b f n := by
    rw [outerScalarDeficit,Nat.cast_sub hle,Nat.cast_mul,hs,ht]
  apply hg.generic_thin_quotient_strata
  · unfold outerScalarDeficit
    omega
  · positivity
  · rw [hs]
    simpa only [show d-1+1=d by omega] using hb.1
  · rw [hs,hjcast]
    simpa only [show d-1+1=d by omega] using hb.2

end Froberg.VectorExpansionOpen
