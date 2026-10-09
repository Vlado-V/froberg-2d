module

public import Quartic.MarkedEndpoints
public import Quartic.CharTwoCertificateBases

@[expose] public section

/-! Characteristic-two initial dimensions for the marked endpoint induction. -/

namespace Quartic

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {K : Type*} [Field K] [CharP K 2]

theorem markedEndpoints_28 : MarkedEndpoints K 28 := by
  refine ⟨CharTwoCertificate28.generic, fun _ => ?_⟩
  rw [UniformEndpoint.lowerEndpoint_eq_table 28 (by decide)]
  exact CharTwoCertificate28.marked_lower

theorem markedEndpoints_29 : MarkedEndpoints K 29 := by
  refine ⟨CharTwoCertificate29.generic, fun _ => ?_⟩
  rw [UniformEndpoint.lowerEndpoint_eq_table 29 (by decide)]
  exact CharTwoCertificate29.marked_lower

theorem markedEndpoints_30 : MarkedEndpoints K 30 := by
  refine ⟨CharTwoCertificate30.generic, fun _ => ?_⟩
  rw [UniformEndpoint.lowerEndpoint_eq_table 30 (by decide)]
  exact CharTwoCertificate30.marked_lower

/-- The finite base certificates discharge every initial obligation for a
three-variable marked transfer starting in dimension 28. -/
theorem markedEndpoints_of_transfer
    (hstep : ∀ n : ℕ, 28 ≤ n → MarkedEndpoints K n → MarkedEndpoints K (n + 3)) :
    ∀ n : ℕ, 28 ≤ n → MarkedEndpoints K n :=
  markedEndpoints_of_three_step 28 markedEndpoints_28 markedEndpoints_29 markedEndpoints_30 hstep

end Quartic
