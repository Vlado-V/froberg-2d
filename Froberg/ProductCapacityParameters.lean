module

public import Froberg.PreparedFiniteProducts
public import Froberg.FixedSlotCapacity
public import Froberg.PreparedCountIdentities

@[expose] public section

/-! The Section 5 counts supply the finite product-row records used by the
common-family construction. Fixed appended quadratic slots are included. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module Filter
open scoped Topology
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem productRowCapacity_of_individual_bounds {w v d : ℕ} {J : Finset ℕ}
    {counts : ℕ → ℕ} (hw : 0<w) (hv : 0<v)
    (hev : ∀ j∈J,Even j) (hdeg : ∀ j∈J,j≤d)
    (hdiag : ∀ j∈J,counts j≤(w.choose j-finrank K X)*(v.choose (d-j)/2))
    (hcross : ∀ j∈J,counts j≤((w+j-1).choose j-finrank K X)*(v+(d-j)-1).choose (d-j))
    (R : ℕ) : ProductRowCapacity (K := K) (X := X) w v d R J counts := by
  refine ⟨hw,hv,hev,hdeg,?_,?_⟩
  · intro r _
    exact hdiag r.val.val r.property.1
  · intro r _
    exact ⟨hcross r.val.val r.property.1,hcross (R-r.val.val) r.property.2.1⟩

lemma tendsto_twice_nat : Tendsto (fun n : ℕ => 2*n) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop N] with n hn
  omega

theorem eventually_product_row_capacities {d : ℕ} (hd : 9≤d) :
    ∀ᶠ w : ℕ in atTop,∀ extra : ℕ,∀ᶠ v : ℕ in atTop,∀ r : ℕ,
      (r : ℝ)<countBeta d*(2*(w : ℝ))^2*(2*(v : ℝ))^(d-2) →
      finrank K X=deletedTargetCount d (2*w) →
      ∀ R : ℕ,ProductRowCapacity (K := K) (X := X) w v d R (activeEvenIndices d)
        (targetLayerCount d (2*w) (2*v) (r+extra)) := by
  have hhigher : ∀ᶠ h : ℕ in atTop,∀ j : activeHigherIndices d,∀ᶠ m : ℕ in atTop,
      higherGeneratorCount d h m j.val≤diagonalProductCount d j.val h m ∧
      higherGeneratorCount d h m j.val≤crossProductCount d j.val h m :=
    eventually_all.mpr (fun j => eventually_higher_finite_product_capacity hd j.property)
  have hquad := tendsto_twice_nat.eventually (eventually_quadratic_finite_product_capacity_add hd)
  have hhigher' := tendsto_twice_nat.eventually hhigher
  filter_upwards [hquad,hhigher',eventually_gt_atTop (0 : ℕ)] with w hquad hhigher hw
  intro extra
  have hvquad := tendsto_twice_nat.eventually (hquad extra)
  have hvhigher := tendsto_twice_nat.eventually (eventually_all.mpr hhigher)
  filter_upwards [hvquad,hvhigher,eventually_gt_atTop (0 : ℕ)] with v hquad hhigher hv
  intro r hr hX R
  have hcap : ∀ j∈activeEvenIndices d,
      targetLayerCount d (2*w) (2*v) (r+extra) j≤diagonalProductCount d j (2*w) (2*v) ∧
      targetLayerCount d (2*w) (2*v) (r+extra) j≤crossProductCount d j (2*w) (2*v) := by
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
