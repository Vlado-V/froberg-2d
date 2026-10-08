import Froberg.PreparedAllEvenCounts

/-! Zero-count positive even rows introduce no additional product capacity.
All nonzero degree counts use the existing literal product bounds. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module Filter
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem product_capacities_individual {w v d : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    (h2 : 2∈J) (h4 : 4∈J) (hJ : ∀ j∈J,2≤j)
    (h : ∀ R,ProductRowCapacity (K := K) (X := X) w v d R J counts) :
    ∀ j∈J,counts j≤(w.choose j-finrank K X)*(v.choose (d-j)/2) ∧
      counts j≤((w+j-1).choose j-finrank K X)*(v+(d-j)-1).choose (d-j) := by
  intro j hj
  let r : ProductRows.Row J (2*j) := ⟨⟨j,by omega⟩,hj,by
    change 2*j-j∈J
    simpa only [show 2*j-j=j by omega] using hj,by
    change 2*j≤2*j
    exact le_rfl⟩
  have hd := (h (2*j)).diagonal r (by dsimp [r];omega)
  refine ⟨hd,?_⟩
  by_cases he : j=2
  · subst j
    let p : ProductRows.Row J 6 := ⟨⟨2,by decide⟩,h2,h4,by decide⟩
    exact ((h 6).cross p (by dsimp [p];omega)).1
  · have hj2 : 2<j := by have := hJ j hj;omega
    let p : ProductRows.Row J (2+j) := ⟨⟨2,by omega⟩,h2,by
      change 2+j-2∈J
      simpa using hj,by
      change 2*2≤2+j
      omega⟩
    have hh := ((h (2+j)).cross p (by dsimp [p];omega)).2
    simpa only [p,Nat.add_sub_cancel_left] using hh

theorem allEven_product_capacities {d w v h n e : ℕ} (hd : 9≤d)
    (hcap : ∀ R,ProductRowCapacity (K := K) (X := X) w v d R (activeEvenIndices d)
      (targetLayerCount d h n e)) :
    ∀ R,ProductRowCapacity (K := K) (X := X) w v d R (allEvenIndices d) (allEvenCount d h n e) := by
  have h4 : 4∈activeEvenIndices d := by
    simp only [activeEvenIndices,if_neg (show ¬d≤8 by omega),Finset.mem_filter,Finset.mem_range]
    exact ⟨by omega,by decide,by decide⟩
  have hi := product_capacities_individual (two_mem_activeEvenIndices (by omega)) h4
    (fun j hj => (activeEvenIndices_bounds (by omega) hj).1) hcap
  intro R
  apply productRowCapacity_of_individual_bounds (hcap 0).positive_output (hcap 0).positive_scalar
    (fun j hj => Nat.even_iff.mpr (mem_allEvenIndices.mp hj).2.2)
    (fun j hj => (mem_allEvenIndices.mp hj).2.1)
  · intro j hj
    by_cases ha : j∈activeEvenIndices d
    · rw [allEvenCount_active h n e ha]
      exact (hi j ha).1
    · simp only [allEvenCount_inactive h n e ha,Nat.zero_le]
  · intro j hj
    by_cases ha : j∈activeEvenIndices d
    · rw [allEvenCount_active h n e ha]
      exact (hi j ha).2
    · simp only [allEvenCount_inactive h n e ha,Nat.zero_le]

theorem eventually_allEven_product_capacities {d : ℕ} (hd : 9≤d) :
    ∀ᶠ w : ℕ in atTop,∀ extra : ℕ,∀ᶠ v : ℕ in atTop,∀ r : ℕ,
      (r : ℝ)<countBeta d*(2*(w : ℝ))^2*(2*(v : ℝ))^(d-2) →
      finrank K X=deletedTargetCount d (2*w) →
      ∀ R,ProductRowCapacity (K := K) (X := X) w v d R (allEvenIndices d)
        (allEvenCount d (2*w) (2*v) (r+extra)) := by
  filter_upwards [eventually_product_row_capacities (K := K) (X := X) hd] with w hw
  intro extra
  filter_upwards [hw extra] with v hv
  intro r hr hX
  exact allEven_product_capacities hd (hv r hr hX)

end Froberg.PreparedParameters
