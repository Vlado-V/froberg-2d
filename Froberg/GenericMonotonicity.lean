module

public import Froberg.GenericDimensions
public import Froberg.FormalHomology
public import Froberg.MonomialCounts
public import Froberg.Endpoint

@[expose] public section

/-! Monotonicity and the two-critical-count reduction for the actual generic
dimensions. The existence of the generic rank opens is established in
`GenericDimensions`; the homology injections are established in `FormalHomology`. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type} [Field K] [Infinite K] {n d r s : ℕ}

omit [Infinite K] in
theorem genericHomology_le_family (hn : 0 < n) (q : Fin r → Forms K n d)
    (hq : LinearIndependent K q) :
    genericHomology K n d r ≤ finrank K (EndpointHomology q) := by
  have ha : coefficientForms K n d r (coefficientCoordinates q) = q :=
    coefficientCoordinates.symm_apply_apply q
  have h := genericHomology_le hn (coefficientCoordinates q) (ha.symm ▸ hq)
  rwa [ha] at h

/-- Actual generic homology is nondecreasing with the number of independent
generators. An optimizing larger tuple and its prefix suffice. -/
theorem genericHomology_mono (hn : 0 < n)
    (hrs : r ≤ s) (hs : s ≤ (n + d - 1).choose d) :
    genericHomology K n d r ≤ genericHomology K n d s := by
  obtain ⟨a, hi, ha⟩ := independent_genericCokernel_attained (K := K) hn hs
  let ι : Fin r ↪ Fin s := ⟨Fin.castLE hrs, Fin.castLE_injective hrs⟩
  have hsmall := genericHomology_le_family hn
    (coefficientForms K n d s a ∘ ι) (hi.comp ι ι.injective)
  have hle := endpointHomology_comp_le_anyChar (coefficientForms K n d s a) hi ι
  rw [genericHomology_eq_at_generic hn a hi ha]
  exact hsmall.trans hle

/-- The two actual critical defects in the paper. -/
def criticalDefect (K : Type) [Field K] (n d : ℕ) : ℕ :=
  max (genericHomology K n d (lowerCount n d))
    (genericCokernel K n d (upperCount n d))

/-- Vanishing of the two critical defects gives the correct generic endpoint
for every admissible number of generators. -/
theorem genericEndpoints_of_criticalDefect_zero (hn : 0 < n)
    (hzero : criticalDefect K n d = 0) :
    ∀ r ≤ (n + d - 1).choose d, GenericEndpoint K n d r := by
  have hall := all_counts_of_two_critical_zeros
    (genericHomology K n d) (genericCokernel K n d) (euler n d)
    ((n + d - 1).choose d) (lowerCount n d) (upperCount n d)
    (lowerCount_le_monomial_count hn d) (upperCount_le_monomial_count hn d)
    (upperCount_le_lowerCount_add_one n d)
    (fun a b hab hb => genericHomology_mono hn hab hb)
    (fun a b hab _ => genericCokernel_antitone hab)
    (fun r hr => generic_euler hn hr) hzero
  intro r hr
  exact (genericEndpoint_iff_genericCokernel hn hr).mpr (hall r hr).1

end Froberg
