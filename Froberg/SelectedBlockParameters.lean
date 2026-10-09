module

public import Froberg.ConcreteCounts
public import Froberg.CountSequences

@[expose] public section

/-! Exact count sequences can be chosen with any eventual condition on
the even block size. The divisibility built into the counts also provides
the fourfold divisibility needed by the small-degree constructions. -/
noncomputable section
namespace Froberg
open Filter

theorem FixedBlockConditions.four_dvd {d k h : ℕ} (H : FixedBlockConditions d k h) :
    4 ∣ h := by
  rw [H.size_eq]
  exact dvd_mul_of_dvd_left ((show 4 ∣ 720720 by decide).trans H.divisible) _

theorem exact_count_sequences_with_block_property {d : ℕ} (hd : 3 ≤ d)
    (lo : ℕ) (P : ℕ → Prop) (hP : ∀ᶠ w : ℕ in atTop,P (2*w)) :
    ∃ k w : ℕ,FixedBlockConditions d k (2*w) ∧ 4 ∣ 2*w ∧ P (2*w) ∧
      ∃ (δ : ℝ) (a f e : Bool → ℕ → ℕ),0 < δ ∧
        (∀ upper n,a upper n ≤ n) ∧
        ∀ᶠ n in atTop,∀ upper : Bool,
          ExactCountConditions d k (2*w) lo n (a upper n) (f upper n) (e upper n) upper ∧
          δ*(n : ℝ)^(2*d-2) < dimensionReserve d (2*w) n (f upper n) := by
  obtain ⟨W,hW⟩ := eventually_atTop.mp hP
  obtain ⟨k,h,hh,H,δ,hδ,hcounts⟩ := exact_count_and_margin_parameters hd lo (2*W)
  obtain ⟨w,hw⟩ := (show 2 ∣ h from (show 2 ∣ 4 by decide).trans H.four_dvd)
  have hw' : h=2*w := hw
  obtain ⟨a,f,e,ha,hc⟩ := choose_exact_count_sequences hcounts
  subst h
  exact ⟨k,w,H,H.four_dvd,hW w (by omega),δ,a,f,e,hδ,ha,hc⟩

end Froberg
