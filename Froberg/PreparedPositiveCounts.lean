import Froberg.PreparedAllEvenCounts

/-! Every occupied positive slot is strictly below the pure top degree.
This remains true after adding any fixed number of quadratic slots. -/
namespace Froberg.PreparedParameters
open Froberg

theorem allEvenCount_positive_lt {d h m e j : ℕ} (hd : 3≤d)
    (hj : 0<allEvenCount d h m e j) : j<d := by
  by_cases ha : j∈activeEvenIndices d
  · exact (activeEvenIndices_bounds hd ha).2.1
  · rw [allEvenCount_inactive h m e ha] at hj
    omega

theorem allEvenCount_positive_even {d h m e j : ℕ} (hd : 3≤d)
    (hj : 0<allEvenCount d h m e j) : 2≤j ∧ j%2=0 := by
  by_cases ha : j∈activeEvenIndices d
  · exact ⟨(activeEvenIndices_bounds hd ha).1,
      Nat.even_iff.mp (activeEvenIndices_bounds hd ha).2.2⟩
  · rw [allEvenCount_inactive h m e ha] at hj
    omega

end Froberg.PreparedParameters
