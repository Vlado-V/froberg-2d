module

public import Froberg.ShiftedProductCapacity

@[expose] public section

/-! Uniform target-module quantification: the numerical thresholds are selected
before choosing the module carrying the deleted-output detector. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Filter Module
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

theorem eventually_allEven_product_capacities_shift_uniform {d : ℕ} (hd : 9≤d) :
    ∀ᶠ w : ℕ in atTop,∀ z extra : ℕ,∀ᶠ v : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],∀ r : ℕ,
      (r : ℝ)<countBeta d*(2*(w : ℝ))^2*((2*v+z : ℕ) : ℝ)^(d-2) →
      finrank K X=deletedTargetCount d (2*w) →
      ∀ R : ℕ,ProductRowCapacity (K := K) (X := X) w v d R (allEvenIndices d)
        (allEvenCount d (2*w) (2*v+z) (r+extra)) := by
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
  intro X _ _ _ r hr hX
  apply allEven_product_capacities hd
  intro R
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


end Froberg.PreparedParameters
