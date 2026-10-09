module

public import Froberg.ActualPreparedComparison
public import Froberg.UniformPreparedC4Selection

@[expose] public section

/-! Actual critical comparison with a cutoff chosen before the field and
before the pure-family projection data. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
namespace Froberg.PreparedTarget
open Froberg PreparedParameters Filter Module MvPolynomial
open scoped Topology

theorem eventually_uniform_actual_prepared_comparison {d k h lo : ℕ}
    (hd : 3≤d) (ho : d%2=1) (hk : 0<k) (hh : h=k*centralHalfBinomial d)
    (hhpos : 0<h)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n,a n≤n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0<δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) :
    ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K] [IsAlgClosed K],
      ∀ pure : OddPureProjectionData K d h (by omega),
      ∀ (O : ℕ → Submodule K (Poly K h))
        (hO : ∀ j∈allEvenIndices d,O j≤Forms K h j),
        HasBasicOpen (m := n) (q := upperCount n d) (f := f n)
          (counts := allEvenCount d h n (e n)) (by omega : 0<d) hO
          (fun j hj => (mem_allEvenIndices.mp hj).2.1) pure.U →
        ∀ (r : ℕ) (idx : Fin r ≃ PreparedParameters.Label (upperCount n d)
          (allEvenIndices d) (allEvenCount d h n (e n+1))),
        HasEnlargedPreparedOpen (m := n) (f := f n) (by omega : 0<d) ho hO
          (fun j hj => (mem_allEvenIndices.mp hj).2.1)
          (fun j hj => (mem_allEvenIndices.mp hj).2.2) idx pure.U →
        Nonempty (LocalComparisonData K (h+n) d
          (adjacentCriticalCount upper (h+n) d) (criticalDefect K n d)) := by
  classical
  by_cases hnum : 0 < topComplementCount d h ∧
      (h : ℝ)/(2*((1+(d-1) : ℕ) : ℝ)) ≤
        (topComplementCount d h : ℝ)/((h+(d-1)-1).choose (d-1) : ℝ)
  · obtain ⟨G,C,ξ,hG,hC,hξ,hselect⟩ := uniform_exact_counts_prepared_c4_selection
      (u := tailGeneratorCount d h) hd ho hk hh hhpos hnum.1 hnum.2
      upper a f e ha hc hδ hreserve 0
    filter_upwards [hselect,hc,exact_counts_outer_below_degree hd upper a f e hc hξ,
      eventually_gt_atTop (0 : ℕ)] with n hn hncount hsmall hnpos
    intro K _ _ _ pure
    have hn := hn K pure.U pure.independent pure.R pure.surjective pure.kernel pure.growth
    intro O hO hbase r idx hlarge
    let hJ : ∀ j∈allEvenIndices d,j≤d := fun j hj => (mem_allEvenIndices.mp hj).2.1
    let heven : ∀ j∈allEvenIndices d,j%2=0 := fun j hj => (mem_allEvenIndices.mp hj).2.2
    letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d)
        (f n) (tailGeneratorCount d h) (allEvenIndices d) (allEvenCount d h n (e n)) O) :=
      FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
    letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d)
        (f n) (tailGeneratorCount d h) (allEvenIndices d) (allEvenCount d h n (e n+1)) O) :=
      FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
    obtain ⟨A,hA,hAgood⟩ := hbase
    obtain ⟨D,hD,hDgood⟩ := hlarge
    obtain ⟨p,hp,hbi,hbo,hbu,hthin,hgrowth,hmodel,hchild⟩ := hn
      (allEvenIndices d) (allEvenCount d h n (e n)) (allEvenCount d h n (e n+1)) O
      hO hJ heven (allEvenCount_le_append hd h n (e n) 1) (by simp only [Nat.add_zero]; exact le_rfl)
      (fun p => LinearIndependent K (zeroScalarEndpointFamily (by omega : 0<d) hO hJ pure.U p.1 p.2))
      A D hA (fun p hp => hAgood p hp) hD
    have hcert := hDgood p hp
    have hcard : upperCount n d+Fintype.card (ProductRows.LayerLabel (allEvenIndices d)
        (allEvenCount d h n (e n)))+f n+tailGeneratorCount d h=
        adjacentCriticalCount upper (h+n) d := by
      have hhcard := exact_odd_comparison_card hd hncount 0
      change Fintype.card (PreparedParameters.Label (upperCount n d) (allEvenIndices d)
        (allEvenCount d h n (e n+0)) ⊕ (Fin (f n) ⊕ Fin (tailGeneratorCount d h)))=_ at hhcard
      simp only [Nat.add_zero,Fintype.card_sum,Fintype.card_fin,PreparedParameters.Label] at hhcard
      simpa only [Nat.add_comm n h,Nat.add_assoc] using hhcard
    exact exists_critical_comparison_of_prepared_odd (by omega) ho hnpos upper
      hO hJ heven (fun j hj => (mem_allEvenIndices.mp hj).1)
      (fun j hj _ => by have hle := hJ j hj; have he := heven j hj; omega)
      (allEvenCount_le_append hd h n (e n) 1) (quadraticExtraLayer hd h n (e n))
      (quadraticExtraLayer_not_old hd h n (e n)) (quadraticExtraLayer_cover hd h n (e n))
      hcard idx pure.U p hcert.leading hcert.private_independent hcert.independent hcert.odd
      hcert.reduction hcert.separation hbi hbo hbu (ξ*(n : ℝ)^d) hsmall hthin
      (C*(n : ℝ)^d) hchild
  · filter_upwards [] with n
    intro K _ _ _ pure
    exact False.elim (hnum ⟨pure.target_positive,pure.ratio⟩)

end Froberg.PreparedTarget
