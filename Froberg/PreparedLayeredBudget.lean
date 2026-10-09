module

public import Froberg.ShiftedCountLimits
public import Froberg.PreparedAllEvenCounts
public import Froberg.HigherRelationCost
public import Froberg.OddCoefficientCount
public import Froberg.LayeredCapacityAsymptotic
public import Froberg.LayeredIntegerBudget
public import Froberg.OddRowAugmentedConstants

@[expose] public section

/-! The actual prepared even slots and ambient relation losses satisfy the
C.4 integer budget. All scalar-variable reserves may be fixed in advance. -/
noncomputable section
namespace Froberg
open Filter Finset Module
open scoped Topology

def preparedEvenSlotCount (d h m e : ℕ) : ℕ :=
  e+∑ j∈activeHigherIndices d,higherGeneratorCount d h m j

theorem preparedEvenSlotCount_eq_card {d : ℕ} (hd : 3≤d) (h m e : ℕ) :
    preparedEvenSlotCount d h m e=
      Fintype.card (ProductRows.LayerLabel (PreparedParameters.allEvenIndices d)
        (PreparedParameters.allEvenCount d h m e)) := by
  have hc := PreparedParameters.allEvenLabel_card hd 0 h m e
  simp only [PreparedParameters.Label,Fintype.card_sum,Fintype.card_fin,Nat.zero_add] at hc
  rw [hc]
  simpa [preparedEvenSlotCount,ProductRows.LayerLabel,Finset.sum_attach] using (sum_targetLayerCount hd h m e).symm

theorem preparedEvenSlotCount_lower_order {d : ℕ} (hd : 3≤d) (h extra : ℕ)
    (e : ℕ → ℕ)
    (he : ∀ᶠ m : ℕ in atTop,(e m : ℝ)<countBeta d*(h : ℝ)^2*(m : ℝ)^(d-2)) :
    Tendsto (fun m : ℕ => (preparedEvenSlotCount d h m (e m+extra) : ℝ)/(m : ℝ)^d)
      atTop (𝓝 0) := by
  have hs : Tendsto (fun m : ℕ =>
      ((extra+∑ j∈activeHigherIndices d,higherGeneratorCount d h m j : ℕ) : ℝ)/(m : ℝ)^d)
      atTop (𝓝 0) := by
    apply auxiliary_counts_lower_order (activeHigherIndices d) (by omega)
      (fun j => (101/100 : ℝ)*higherCountGamma d j*(h : ℝ)^j)
      (fun j => d-j) extra
    · intro j _
      exact mul_nonneg (mul_nonneg (by norm_num) (higherCountGamma_pos d j).le) (by positivity)
    · intro j hj
      have := (mem_filter.mp hj).2
      omega
  have ht := (quadraticCount_lower_order hd h e he).add hs
  simp only [add_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall fun m => by
    simp only [preparedEvenSlotCount,Nat.cast_add,Nat.cast_sum]
    ring

theorem preparedEvenSlots_shift_lower_order {d : ℕ} (hd : 3≤d) (h extra z : ℕ)
    (e : ℕ → ℕ)
    (he : ∀ᶠ m : ℕ in atTop,(e m : ℝ)<countBeta d*(h : ℝ)^2*(m : ℝ)^(d-2)) :
    Tendsto (fun m : ℕ =>
      (Fintype.card (ProductRows.LayerLabel (PreparedParameters.allEvenIndices d)
        (PreparedParameters.allEvenCount d h (m+z) (e (m+z)+extra))) : ℝ)/(m : ℝ)^d)
      atTop (𝓝 0) := by
  simpa only [←preparedEvenSlotCount_eq_card hd] using
    normalized_limit_shift (preparedEvenSlotCount_lower_order hd h extra e he) z

theorem thinSlices_positive_integer_base (T k : ℕ) (C : ℝ) (hC : 0≤C)
    (hs : 0<BilinearCovectorStrata.thinSlices T C k) :
    BilinearCovectorStrata.thinSlices T C k+⌊C⌋₊*k≤T := by
  have hh : ⌊C⌋₊*k≤⌈C*(k : ℝ)⌉₊ := by
    have hr := (mul_le_mul_of_nonneg_right (Nat.floor_le hC) (Nat.cast_nonneg k)).trans
      (Nat.le_ceil (C*(k : ℝ)))
    exact_mod_cast hr
  unfold BilinearCovectorStrata.thinSlices at *
  omega

theorem scalarReserveCount_eq_ordinary (d m : ℕ) :
    scalarReserveCount d m=⌊oddRowExtraDensity d*(m : ℝ)^d⌋₊ := rfl

theorem min_higher_capacity_eq (d m : ℕ) :
    min (scalarReserveCount d m) ⌊oddRowExtraDensity d*(m : ℝ)^d⌋₊=
      scalarReserveCount d m := by rw [←scalarReserveCount_eq_ordinary];exact min_self _

/-- This supplies every integer-rate and lower-order hypothesis of the
positive-stratum uniform quotient-slice theorem. The only source-dimension
input is its literal bound by the full odd homogeneous coefficient space. -/
theorem eventually_prepared_layered_budget {d : ℕ} (hd : 3≤d) (h u z extra : ℕ)
    (e a : ℕ → ℕ) (Cbottom : ℝ) (hCbottom : 0<Cbottom)
    (he : ∀ᶠ m : ℕ in atTop,(e m : ℝ)<countBeta d*(h : ℝ)^2*(m : ℝ)^(d-2))
    (ha : ∀ᶠ m : ℕ in atTop,a m≤oddCoefficientCount d h (m+z)) :
    ∃ (L : ℕ → ℕ) (ξ : ℝ),0<ξ ∧ ∀ᶠ m : ℕ in atTop,
      0<L m ∧ L m≤⌊Cbottom*(m : ℝ)^d⌋₊ ∧
      L m ≤ min (scalarReserveCount d m) ⌊oddRowExtraDensity d*(m : ℝ)^d⌋₊ ∧
      2*(higherRelationCost d h u (m+z)+a m+
        Fintype.card (ProductRows.LayerLabel (PreparedParameters.allEvenIndices d)
          (PreparedParameters.allEvenCount d h (m+z) (e (m+z)+extra))))+1≤L m ∧
      (∀ j r : ℕ,j≤BilinearCovectorStrata.thinSlices j (ξ*(m : ℝ)^d) r+
          ⌈ξ*(m : ℝ)^d*(r : ℝ)⌉₊ ∧
          ⌈ξ*(m : ℝ)^d*(r : ℝ)⌉₊≤L m*r/2) ∧
      ∀ T k : ℕ,0<BilinearCovectorStrata.thinSlices T (Cbottom*(m : ℝ)^d) k →
        BilinearCovectorStrata.thinSlices T (Cbottom*(m : ℝ)^d) k+
          ⌊Cbottom*(m : ℝ)^d⌋₊*k≤T := by
  let q := fun m => Fintype.card (ProductRows.LayerLabel (PreparedParameters.allEvenIndices d)
    (PreparedParameters.allEvenCount d h (m+z) (e (m+z)+extra)))
  have hq : Tendsto (fun m : ℕ => (q m : ℝ)/(m : ℝ)^d) atTop (𝓝 0) :=
    preparedEvenSlots_shift_lower_order hd h extra z e he
  have hH := normalized_limit_shift (higherRelationCost_shadow_lower_order hd h u) z
  have hsource : Tendsto (fun m : ℕ => (a m : ℝ)/(m : ℝ)^d) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) _
      (normalized_limit_shift (oddCoefficientCount_lower_order (d := d) (by omega) h) z)
    exact ha.mono fun m hm => div_le_div_of_nonneg_right (by exact_mod_cast hm) (by positivity)
  have hC : Tendsto (fun m : ℕ => (⌊Cbottom*(m : ℝ)^d⌋₊ : ℝ)/(m : ℝ)^d)
      atTop (𝓝 Cbottom) := floor_normalized_limit _ (by omega) _
        (Eventually.of_forall fun m => by positivity) (scaled_power_normalized_limit _ _)
  obtain ⟨L,ξ,hξ,hgood⟩ := layered_capacity_eventually (by omega : 0<d)
    (fun m => higherRelationCost d h u (m+z)) a q
    (fun m => ⌊Cbottom*(m : ℝ)^d⌋₊) Cbottom (scalarReserveDensity d)
    hCbottom (scalarReserveDensity_pos d) hH hsource hq hC
  refine ⟨L,ξ,hξ,?_⟩
  filter_upwards [hgood] with m hm
  refine ⟨hm.1,hm.2.1,?_,hm.2.2.2.1,?_,?_⟩
  · rw [min_higher_capacity_eq]
    exact hm.2.2.1
  · intro j r
    apply thinSlices_integer_loss j (L m) (ξ*(m : ℝ)^d) _ r
    simpa only [Nat.cast_one,mul_one] using hm.2.2.2.2 1 (by omega)
  · intro T k hk
    exact thinSlices_positive_integer_base T k _ (by positivity) hk

end Froberg
