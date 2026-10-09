module

public import Quartic.SharpCertificate.Certificate

@[expose] public section

/-! Exact counts of checked sharp edges, compressed intervals, and integer edge values. -/

namespace Quartic.SharpCertificate

open Quartic.FiniteCounts Quartic.ProfileCertificate Quartic.HullCertificate

/-- Number of indexed core/edge pairs in one configuration. -/
def configurationEdgeCount (c : ℕ) : ℕ := 6 * (coreA c + 1)

theorem configurationEdgeCount_eq_card (c : ℕ) :
    configurationEdgeCount c = Fintype.card (Fin (coreA c + 1) × Fin 6) := by
  simp only [configurationEdgeCount, Fintype.card_prod, Fintype.card_fin]
  omega

/-- Number of actual intervals passed to the certificate checker. -/
def configurationIntervalCount (m q c : ℕ) : ℕ :=
  ((List.range (coreA c + 1)).map fun i =>
    ((List.finRange 6).map fun edge =>
      (automaticIntervals (scalars m q c) (edgeLower m c i edge) (edgeUpper m c i edge)).length).sum).sum

/-- Number of integer edge values, counting each core/edge index separately. -/
def configurationValueCount (m c : ℕ) : ℕ :=
  ((List.range (coreA c + 1)).map fun i =>
    ((List.finRange 6).map fun edge =>
      (edgeUpper m c i edge - edgeLower m c i edge + 1).toNat).sum).sum

/-- Sum over the 89 dimensions and both parent endpoints. -/
def rangeTotal (f : ℕ → Bool → ℕ) : ℕ :=
  ((List.range 89).map fun index => f (index + 41) false + f (index + 41) true).sum

end Quartic.SharpCertificate
