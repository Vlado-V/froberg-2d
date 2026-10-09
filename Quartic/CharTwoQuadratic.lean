module

public import Quartic.MarkedQuadraticTransfer
public import Quartic.MarkedEndpointBases

@[expose] public section

/-! Generic quartic maximal rank in characteristic two, obtained by propagating
the three checked marked base dimensions with the marked transfer. -/
noncomputable section
namespace Quartic.CharTwoQuadratic
variable {K : Type*} [Field K] [Infinite K] [IsAlgClosed K] [CharP K 2]

/-- All counts are generically exact, and a square survives at each positive
lower endpoint, in every dimension at least 28. -/
theorem markedEndpoints (n : ℕ) (hn : 28 ≤ n) : MarkedEndpoints K n :=
  Quartic.markedEndpoints_of_transfer
    (fun m hm hchild => MarkedQuadraticTransfer.marked_transfer m hm hchild) n hn

/-- Generic quartic maximal rank for every admissible quadratic count. -/
theorem generic (n : ℕ) (hn : 28 ≤ n) (r : ℕ) (hr : r ≤ (n + 1).choose 2) :
    GenericQuartic K n r :=
  (markedEndpoints n hn).1 r hr

end Quartic.CharTwoQuadratic
