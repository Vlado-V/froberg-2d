module

public import Froberg.ShiftedCountLimits
public import Froberg.PreparedAllEvenProducts

@[expose] public section

/-! Fixed private variables do not consume the strict product capacity margin
in the remaining core variables. The output size is chosen before the shift. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem eventually_quadratic_product_capacity_shift {d : ℕ} (hd : 9≤d) :
    ∀ᶠ h : ℕ in atTop,∀ z extra : ℕ,∀ᶠ m : ℕ in atTop,∀ r : ℕ,
      (r : ℝ)<countBeta d*(h : ℝ)^2*((m+z : ℕ) : ℝ)^(d-2) →
      r+extra≤diagonalProductCount d 2 h m ∧ r+extra≤crossProductCount d 2 h m := by
  filter_upwards [eventually_product_capacity_majorant hd (two_mem_activeEvenIndices (by omega)),
    eventually_gt_atTop (0 : ℕ)] with h hh hh0
  intro z extra
  have hΓ : 0<countGammaTwo d :=
    (countTauFour_pos (by omega)).trans_le (countTauFour_le_gamma d)
  have hβ : 0≤countBeta d := by unfold countBeta;positivity
  have hc : countBeta d<(253/250 : ℝ)*countGammaTwo d := by unfold countBeta;nlinarith
  have hh2 : 0<(h : ℝ)^2 := pow_pos (by exact_mod_cast hh0) 2
  have he := eventually_shifted_ceil_add_le_ceil (by omega : 0<d-2)
    (mul_nonneg hβ hh2.le) (mul_lt_mul_of_pos_right hc hh2) z extra
  filter_upwards [hh,he] with m hm hem
  intro r hr
  have hrceil : r≤⌈countBeta d*(h : ℝ)^2*((m+z : ℕ) : ℝ)^(d-2)⌉₊ := by
    exact_mod_cast hr.le.trans (Nat.le_ceil _)
  have hdiag : r+extra≤diagonalProductCount d 2 h m :=
    (Nat.add_le_add_right hrceil extra).trans (hem.trans (by simpa [intermediateDensity] using hm))
  exact ⟨hdiag,hdiag.trans (diagonalProductCount_le_cross (by omega) (by omega))⟩

theorem eventually_higher_product_capacity_shift {d j : ℕ} (hd : 9≤d)
    (hj : j∈activeHigherIndices d) :
    ∀ᶠ h : ℕ in atTop,∀ z : ℕ,∀ᶠ m : ℕ in atTop,
      higherGeneratorCount d h (m+z) j≤diagonalProductCount d j h m ∧
      higherGeneratorCount d h (m+z) j≤crossProductCount d j h m := by
  have hb := activeEvenIndices_bounds (by omega : 3≤d) (Finset.mem_filter.mp hj).1
  have hj4 := (Finset.mem_filter.mp hj).2
  filter_upwards [eventually_product_capacity_majorant hd (Finset.mem_filter.mp hj).1,
    eventually_gt_atTop (0 : ℕ)] with h hh hh0
  intro z
  have hγ := higherCountGamma_pos d j
  have hp : 0<(h : ℝ)^j := pow_pos (by exact_mod_cast hh0) j
  have hc : (101/100 : ℝ)*higherCountGamma d j < (253/250 : ℝ)*higherCountGamma d j := by nlinarith
  have he := eventually_shifted_ceil_add_le_ceil (by omega : 0<d-j)
    (by positivity : 0≤((101/100 : ℝ)*higherCountGamma d j)*(h : ℝ)^j)
    (mul_lt_mul_of_pos_right hc hp) z 0
  filter_upwards [hh,he] with m hm hem
  have hdiag : higherGeneratorCount d h (m+z) j≤diagonalProductCount d j h m := by
    simp only [Nat.add_zero] at hem
    exact hem.trans (by simpa only [intermediateDensity,if_neg (show j≠2 by omega)] using hm)
  exact ⟨hdiag,hdiag.trans (diagonalProductCount_le_cross (by omega) hb.2.1)⟩

namespace PreparedParameters
open Module
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem eventually_product_row_capacities_shift {d : ℕ} (hd : 9≤d) :
    ∀ᶠ w : ℕ in atTop,∀ z extra : ℕ,∀ᶠ v : ℕ in atTop,∀ r : ℕ,
      (r : ℝ)<countBeta d*(2*(w : ℝ))^2*((2*v+z : ℕ) : ℝ)^(d-2) →
      finrank K X=deletedTargetCount d (2*w) →
      ∀ R : ℕ,ProductRowCapacity (K := K) (X := X) w v d R (activeEvenIndices d)
        (targetLayerCount d (2*w) (2*v+z) (r+extra)) := by
  have hhigher : ∀ᶠ h : ℕ in atTop,∀ j : activeHigherIndices d,∀ z : ℕ,∀ᶠ m : ℕ in atTop,
      higherGeneratorCount d h (m+z) j.val≤diagonalProductCount d j.val h m ∧
      higherGeneratorCount d h (m+z) j.val≤crossProductCount d j.val h m :=
    eventually_all.mpr (fun j => eventually_higher_product_capacity_shift hd j.property)
  have hquad := tendsto_twice_nat.eventually (eventually_quadratic_product_capacity_shift hd)
  have hhigher' := tendsto_twice_nat.eventually hhigher
  filter_upwards [hquad,hhigher',eventually_gt_atTop (0 : ℕ)] with w hquad hhigher hw
  intro z extra
  have hvquad := tendsto_twice_nat.eventually (hquad z extra)
  have hvhigher := tendsto_twice_nat.eventually (eventually_all.mpr (fun j => hhigher j z))
  filter_upwards [hvquad,hvhigher,eventually_gt_atTop (0 : ℕ)] with v hquad hhigher hv
  intro r hr hX R
  have hcap : ∀ j∈activeEvenIndices d,
      targetLayerCount d (2*w) (2*v+z) (r+extra) j≤diagonalProductCount d j (2*w) (2*v) ∧
      targetLayerCount d (2*w) (2*v+z) (r+extra) j≤crossProductCount d j (2*w) (2*v) := by
    intro j hj
    by_cases hj2 : j=2
    · subst j
      simpa only [targetLayerCount,ite_true] using hquad r
        (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hr)
    · have hjhigher := activeEven_ne_two_is_higher (by omega : 3≤d) ⟨j,hj⟩ hj2
      simpa only [targetLayerCount,if_neg hj2] using hhigher ⟨j,hjhigher⟩
  apply productRowCapacity_of_individual_bounds hw hv
    (fun j hj => (activeEvenIndices_bounds (by omega) hj).2.2)
    (fun j hj => (activeEvenIndices_bounds (by omega) hj).2.1.le)
  · intro j hj
    simpa only [diagonalProductCount,diagonalOutputCount,show 2*w/2=w by omega,
      show 2*v/2=v by omega,
      hX] using (hcap j hj).1
  · intro j hj
    simpa only [crossProductCount,show 2*w/2=w by omega,show 2*v/2=v by omega,hX]
      using (hcap j hj).2


theorem eventually_allEven_product_capacities_shift {d : ℕ} (hd : 9≤d) :
    ∀ᶠ w : ℕ in atTop,∀ z extra : ℕ,∀ᶠ v : ℕ in atTop,∀ r : ℕ,
      (r : ℝ)<countBeta d*(2*(w : ℝ))^2*((2*v+z : ℕ) : ℝ)^(d-2) →
      finrank K X=deletedTargetCount d (2*w) →
      ∀ R,ProductRowCapacity (K := K) (X := X) w v d R (allEvenIndices d)
        (allEvenCount d (2*w) (2*v+z) (r+extra)) := by
  filter_upwards [eventually_product_row_capacities_shift (K := K) (X := X) hd] with w hw
  intro z extra
  filter_upwards [hw z extra] with v hv
  intro r hr hX
  exact allEven_product_capacities hd (hv r hr hX)

end PreparedParameters
end Froberg
