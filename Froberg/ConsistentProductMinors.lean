import Froberg.ProductMinors

/-! Product minors from consistent factor choices, allowing square columns. -/
noncomputable section
namespace Froberg.ProductMinors

variable {K α τ ι : Type*} [CommRing K]

/-- Choices on repeated labels extend precisely when they agree on each label fiber. -/
theorem exists_choices_of_factorsThrough (labels : ι × Bool → α)
    (choices : ι × Bool → τ →₀ ℕ) (h : choices.FactorsThrough labels) :
    ∃ c : α → τ →₀ ℕ, ∀ p, c (labels p) = choices p := by
  exact ⟨Function.extend labels choices (fun _ => 0),
    h.extend_apply (fun _ => 0)⟩

/-- A matched square column is permitted: its two occurrences of the label must
select the same monomial. Distinct columns may also share a label if their
choices agree. The conclusion concerns the actual generic polynomial matrix. -/
theorem consistent_productMinor_ne_zero [Nontrivial K] [Fintype ι] [DecidableEq ι]
    [DecidableEq (τ →₀ ℕ)] (terms : α → Finset (τ →₀ ℕ))
    (labels : ι × Bool → α) (choices : ι × Bool → τ →₀ ℕ)
    (hconsistent : choices.FactorsThrough labels)
    (hchoices : ∀ p, choices p ∈ terms (labels p))
    (hinj : Function.Injective (fun i => choices (i,false) + choices (i,true))) :
    (productMinor (K := K) terms (fun i => labels (i,false)) (fun i => labels (i,true))
      (fun i => choices (i,false) + choices (i,true))).det ≠ 0 := by
  obtain ⟨c,hc⟩ := exists_choices_of_factorsThrough labels choices hconsistent
  have h := productMinor_ne_zero (K := K) terms
    (fun i => labels (i,false)) (fun i => labels (i,true)) c
    (fun i => by rw [hc]; exact hchoices (i,false))
    (fun i => by rw [hc]; exact hchoices (i,true))
    (by simpa only [hc] using hinj)
  simpa only [hc] using h

end Froberg.ProductMinors
