module

public import Froberg.FieldUniformPrivateModel
public import Froberg.CountedPrivateThinOpen
public import Froberg.AugmentedOuterCapacity

@[expose] public section

/-! Exact-count private opens with constants and cutoffs uniform over all
infinite fields. Each field is chosen only after the numerical threshold. -/
noncomputable section
namespace Froberg
open Filter Module MvPolynomial VectorExpansionOpen BilinearScalarFamily
open scoped Topology

theorem uniform_exact_counts_private_strict_open
    {d k h lo b : ℕ} (hd : 3 ≤ d) (hk : 0 < k) (hh : h=k*centralHalfBinomial d)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n,a n ≤ n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) :
    ∃ G : ℝ,0 < G ∧ ∀ᶠ n in atTop,∀ (K : Type) [Field K] [Infinite K],
      ∃ D : MvPolynomial (VectorParameters.Index h n (d-1) (f n+b)) K,
        (∃ p,eval p D ≠ 0) ∧ ∀ p,eval p D ≠ 0 →
          StrictModel (VectorParameters.generators p) d (G*(n : ℝ)^d) := by
  obtain ⟨hat,hzt,har,hzr⟩ := exact_conditions_core_limits hd hk hh upper a f e ha hc
  have hd' : d-1+1=d := by omega
  have hh' : h=k*(2*(d-1)+1).choose (d-1) := by
    simpa only [centralHalfBinomial,show 2*(d-1)+1=2*d-1 by omega] using hh
  obtain ⟨G,hG,hopen⟩ := PrivateColumns.eventually_field_uniform_private_strict_open (b := b)
    hk (by omega : 2 ≤ d-1) hh' a (fun n => n-a n) hat hzt
    (by simpa only [hd'] using har) (by simpa only [hd'] using hzr)
    (fun n => Nat.add_sub_of_le (ha n))
  refine ⟨G,hG,?_⟩
  filter_upwards [hopen,hc] with n hn hcn
  intro K _ _
  have hfield := hn K
  have hcard : Fintype.card (OuterInjection.Labels k (a n) (d-1) ⊕ Fin b)=f n+b := by
    rw [hcn.outer_eq]
    simp only [OuterInjection.Labels,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,
      Sym.card_sym_eq_choose]
  rw [hcard,Nat.add_sub_of_le (ha n),hd'] at hfield
  exact hfield


namespace VectorExpansionOpen
open Quartic VectorMultiplicationCoordinates

theorem eventually_field_uniform_counted_outer_strata {d h b : ℕ} (hd : 3 ≤ d) (hh : 0 < h)
    (f : ℕ → ℕ) (G : ℝ) (hG : 0 < G) {δ : ℝ} (hδ : 0 < δ)
    (hf : Tendsto (fun n : ℕ => (f n : ℝ)/(n : ℝ)^(d-1)) atTop
      (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))))
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ n in atTop,∀ (K : Type) [Field K] [Infinite K],
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
  intro K _ _ g hg
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


theorem eventually_field_uniform_augmented_outer_capacity {d h b : ℕ} (hd : 3 ≤ d)
    (f extra : ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hextra : Tendsto (fun n : ℕ => (extra n : ℝ)/(n : ℝ)^(d-1)) atTop (𝓝 0))
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) :
    ∀ᶠ n : ℕ in atTop,∀ (K : Type) [Field K] [Infinite K],∀ (G : ℝ) (g : Fin (f n+b) → Rows K h n (d-1)),
      StrictModel g d G →
      (upperCount n d+extra n)*finrank K (Source g) ≤ finrank K (Target g d) := by
  filter_upwards [outer_augmented_deficit_eventually_positive (b := b) hd f extra hδ hextra hreserve,
    eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  intro K _ _ G g hg
  have hs : (finrank K (Source g) : ℝ)=outerSourceCount d h b f n := by
    rw [hg.source_real_count hnpos]
    unfold outerSourceCount
    push_cast
    ring
  have ht : (finrank K (Target g d) : ℝ)=outerTargetCount d h b f n := by
    rw [hg.target_real_count hnpos,show d-1+d=2*d-1 by omega]
    unfold outerTargetCount
    push_cast
    rfl
  have hle : ((upperCount n d+extra n : ℕ) : ℝ)*finrank K (Source g)≤finrank K (Target g d) := by
    rw [hs,ht]
    linarith
  exact_mod_cast hle


end VectorExpansionOpen

theorem uniform_exact_counts_private_thin_open
    {d k h lo b : ℕ} (hd : 3 ≤ d) (hk : 0 < k)
    (hh : h=k*centralHalfBinomial d) (hhpos : 0 < h)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n,a n ≤ n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0 < δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) :
    ∃ G C : ℝ,0 < G ∧ 0 < C ∧ ∀ᶠ n in atTop,∀ (K : Type) [Field K] [Infinite K],
      ∃ D : MvPolynomial (VectorParameters.Index h n (d-1) (f n+b)) K,
        (∃ p,eval p D ≠ 0) ∧ ∀ p,eval p D ≠ 0 →
          StrictModel (VectorParameters.generators p) d (G*(n : ℝ)^d) ∧
          HasThinQuotientOpen (quotientMultiplication (VectorParameters.generators p) d)
            (upperCount n d) (outerScalarDeficit (VectorParameters.generators p)) (C*(n : ℝ)^d) := by
  obtain ⟨G,hG,hopen⟩ := uniform_exact_counts_private_strict_open (b := b) hd hk hh upper a f e ha hc
  obtain ⟨C,hC,hthin⟩ := eventually_field_uniform_counted_outer_strata (b := b) hd hhpos f G hG hδ
    (exact_conditions_outer_limit hd upper a f e hc) hreserve
  refine ⟨G,C,hG,hC,?_⟩
  filter_upwards [hopen,hthin] with n hn ht
  intro K _ _
  obtain ⟨D,hD,hgood⟩ := hn K
  exact ⟨D,hD,fun p hp => ⟨hgood p hp,ht K _ (hgood p hp)⟩⟩


end Froberg
