module

public import Froberg.CountedOuterStrata

@[expose] public section

/-! B.2 and the thin B.3 conclusion on the exact-count full coefficient open. -/
noncomputable section
namespace Froberg
open Filter Module MvPolynomial VectorExpansionOpen BilinearScalarFamily
open scoped Topology

theorem exact_counts_private_thin_open {K : Type*} [Field K] [Infinite K]
    {d k h lo b : ℕ} (hd : 3 ≤ d) (hk : 0 < k)
    (hh : h=k*centralHalfBinomial d) (hhpos : 0 < h)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n,a n ≤ n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0 < δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) :
    ∃ G C : ℝ,0 < G ∧ 0 < C ∧ ∀ᶠ n in atTop,
      ∃ D : MvPolynomial (VectorParameters.Index h n (d-1) (f n+b)) K,
        (∃ p,eval p D ≠ 0) ∧ ∀ p,eval p D ≠ 0 →
          StrictModel (VectorParameters.generators p) d (G*(n : ℝ)^d) ∧
          HasThinQuotientOpen (quotientMultiplication (VectorParameters.generators p) d)
            (upperCount n d) (outerScalarDeficit (VectorParameters.generators p)) (C*(n : ℝ)^d) := by
  obtain ⟨G,hG,hopen⟩ := exact_counts_private_strict_open (K := K) (b := b) hd hk hh upper a f e ha hc
  obtain ⟨C,hC,hthin⟩ := eventually_counted_outer_strata (K := K) (b := b) hd hhpos f G hG hδ
    (exact_conditions_outer_limit hd upper a f e hc) hreserve
  refine ⟨G,C,hG,hC,?_⟩
  filter_upwards [hopen,hthin] with n hn ht
  obtain ⟨D,hD,hgood⟩ := hn
  exact ⟨D,hD,fun p hp => ⟨hgood p hp,ht _ (hgood p hp)⟩⟩

end Froberg
