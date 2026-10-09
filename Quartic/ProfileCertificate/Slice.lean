module

public import Quartic.ProfileCertificate.Core

@[expose] public section

/-! The exact bounded predicate shared by the parallel profile checks. -/

namespace Quartic.ProfileCertificate

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exactly the remaining binders of `ConfigurationValid` at a fixed `i`. -/
def ConfigurationSlice (m q c i : ℕ) : Prop :=
  ∀ n₁ : Fin (freeW m c + 1),
  ∀ n₂ : Fin (n₁.val + 1), ∀ n₃ : Fin (n₂.val + 1),
  profileDim i n₁ n₂ n₃ ≠ 0 →
  profileDim i n₁ n₂ n₃ ≠ totalA m c →
  ProfileBound m q c i n₁ n₂ n₃

instance (m q c i : ℕ) : Decidable (ConfigurationSlice m q c i) := by
  unfold ConfigurationSlice
  infer_instance

end Quartic.ProfileCertificate
