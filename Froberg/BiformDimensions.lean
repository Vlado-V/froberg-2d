import Froberg.BiformActions

noncomputable section
namespace Froberg
open Module TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type*} [Field K]
variable {h n : ℕ}

/-- The exact dimension of a two-block homogeneous coefficient space. -/
theorem finrank_biform (hh : 0<h) (hn : 0<n) (a c : ℕ) :
    finrank K (Forms K h a ⊗[K] Forms K n c)=
      (h+a-1).choose a*(n+c-1).choose c := by
  rw [finrank_tensorProduct,finrank_forms K h a hh,finrank_forms K n c hn]

theorem finrank_biform_pos (hh : 0<h) (hn : 0<n) (a c : ℕ) :
    0<finrank K (Forms K h a ⊗[K] Forms K n c) := by
  rw [finrank_biform hh hn]
  exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))

end Froberg
