module

public import Froberg.ParityProfileRows
public import Froberg.RetainedSubspaceGrowth

@[expose] public section

/-! The retained scalar row estimate for B.4, transferred to every actual
homogeneous polynomial subspace by initial monomials. -/
noncomputable section
namespace Froberg
open Finset Module MvPolynomial MonomialExpansion

def parityProfileRetained {n : ℕ} (S : Finset (Fin n)) (p j : ℕ)
    (a : Fin n →₀ ℕ) : Prop := partialDegree S a % 2 ≠ p ∧ partialDegree S a ≠ j

instance {n : ℕ} (S : Finset (Fin n)) (p j : ℕ) : DecidablePred (parityProfileRetained S p j) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem exists_parity_profile_growth_threshold {d : ℕ} (hd : 9 ≤ d) (e : ℕ) :
    ∃ m₀ : ℕ, ∀ (K : Type*) [Field K] (n : ℕ) (S : Finset (Fin n)),
      m₀ ≤ S.card → S.card ≤ Sᶜ.card → Sᶜ.card ≤ S.card+1 →
      ∀ U : Submodule K (Poly K n), U ≤ Forms K n e → ∀ p < 2, ∀ j : ℕ,
        (n+(e+d)-1).choose (e+d) * finrank K U ≤
          4 * (n+e-1).choose e * finrank K
            ((U * Forms K n d).map (retainMonomials (parityProfileRetained S p j))) := by
  obtain ⟨m₀,hm₀⟩ := exists_parity_profile_row_threshold hd e
  refine ⟨max 1 m₀,?_⟩
  intro K _ n S hm hle hupper U hU p hp j
  have hpos : 0<S.card := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hm)
  have hcard : S.card≤n := by simpa using card_le_univ S
  have hn : 0<n := hpos.trans_le hcard
  have h := retained_homogeneous_subspace_growth (K := K) (d := d) hn
    (parityProfileRetained S p j) 1 4 (U := U) (hU := hU)
  simp only [one_mul] at h
  apply h
  intro α
  have hr := hm₀ n S ((le_max_right _ _).trans hm) hle hupper α.val (degree_val α) p hp j
  convert hr using 1
  congr 1
  change (∑ β ∈ (Finset.univ : Finset (Degree n (e+d))).filter
    (fun β => partialDegree S β.val % 2 ≠ p ∧ partialDegree S β.val ≠ j), weight β.val α.val) = _
  rw [Finset.sum_filter]
  rw [Finset.sum_filter]
  exact sum_coe_sort (exponents n (e+d))
    (fun β : Fin n →₀ ℕ => if partialDegree S β % 2 ≠ p ∧ partialDegree S β ≠ j then weight β α.val else 0)

end Froberg
