import Froberg.PrefixSurjectivity
import Froberg.PrefixPrediction

/-! The complete lower-degree input: generic forms have the predicted Hilbert
function through degree `2*d-1` in sufficiently many variables. -/
noncomputable section
namespace Froberg
open MvPolynomial Finset
variable {K : Type*} [Field K] [Infinite K] {n d e r : ℕ}

/-- Both sides of the prefix maximal-rank problem have actual witnesses. -/
theorem exists_prefix_expected_hilbert (hn : 0 < n) (hed : e < d)
    (hlarge : (e + d).choose e * ((e + d).choose e * d.choose e) ≤ n) :
    ∃ f : Fin r → Forms K n d,
      hilbertFunction (familySpace f) (d + e) =
        (n + (d + e) - 1).choose (d + e) - r * (n + e - 1).choose e := by
  by_cases hr : r * (n + e - 1).choose e ≤ (n + (d + e) - 1).choose (d + e)
  · obtain ⟨f, hf⟩ := exists_prefix_injective_of_large_variables (K := K) hn hed hlarge hr
    exact ⟨f, prefix_hilbert_of_injective hn f hf⟩
  · obtain ⟨f, hf⟩ := exists_prefix_surjective_of_large_variables (K := K) (r := r) hn hed hlarge (by omega)
    refine ⟨f, ?_⟩
    rw [prefix_hilbert_of_surjective hn f hf]
    omega

/-- Maximal prefix rank is attained on a nonempty principal open. -/
theorem genericHilbertAt_prefix_of_large_variables (hn : 0 < n) (hed : e < d)
    (hlarge : (e + d).choose e * ((e + d).choose e * d.choose e) ≤ n) :
    GenericHilbertAt K n d r (d + e) := by
  obtain ⟨f, hf⟩ := exists_prefix_expected_hilbert (K := K) (r := r) hn hed hlarge
  let a₀ := coefficientCoordinates f
  have ha₀ : coefficientForms K n d r a₀ = f := coefficientCoordinates.symm_apply_apply f
  have h₀ : hilbertFunction (coefficientSpace K n d r a₀) (d + e) =
      (n + (d + e) - 1).choose (d + e) - r * (n + e - 1).choose e := by
    change hilbertFunction (familySpace (coefficientForms K n d r a₀)) (d + e) = _
    rw [ha₀]
    exact hf
  obtain ⟨D, hD, hgood⟩ := prefix_lower_bound_principal_open hn a₀ h₀
  refine ⟨D, ⟨a₀, hD⟩, ?_⟩
  intro a ha
  rw [predictedHilbertFunction_prefix hn hed]
  exact hgood a ha

/-- A concrete uniform variable threshold for the entire prefix. -/
def prefixThreshold (d : ℕ) : ℕ :=
  max 1 ((range d).sup (fun e => (e + d).choose e * ((e + d).choose e * d.choose e)))

theorem prefixThreshold_pos (d : ℕ) : 0 < prefixThreshold d :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

/-- The lower-degree theorem used by the manuscript, including one common open
for all degrees and with no external maximal-rank assumption. -/
theorem genericHilbertThrough_prefix {d : ℕ} (hd : 0 < d) {n : ℕ}
    (hn : prefixThreshold d ≤ n) (r : ℕ) :
    GenericHilbertThrough K n d r (2 * d - 1) := by
  have hnpos : 0 < n := (prefixThreshold_pos d).trans_le hn
  apply (genericHilbertThrough_iff _).mpr
  intro j hj
  by_cases hjd : j < d
  · exact genericHilbertAt_below_degree hnpos hjd
  · have hed : j - d < d := by omega
    have hlarge : ((j - d) + d).choose (j - d) *
        (((j - d) + d).choose (j - d) * d.choose (j - d)) ≤ n := by
      have h := Finset.le_sup (f := fun e =>
        (e + d).choose e * ((e + d).choose e * d.choose e)) (mem_range.mpr hed)
      exact h.trans ((le_max_right _ _).trans hn)
    have h := genericHilbertAt_prefix_of_large_variables (K := K) (r := r) hnpos hed hlarge
    simpa only [Nat.add_sub_of_le (by omega : d ≤ j)] using h

end Froberg
