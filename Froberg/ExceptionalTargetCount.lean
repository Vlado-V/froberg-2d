module

public import Froberg.MixedPacking
public import Froberg.CommonMultipleCount

@[expose] public section

/-! Uniform exceptional-target count for the attached monomial relations. -/
noncomputable section
namespace Froberg.MixedExterior
open Module
variable {K α : Type*} [Field K] [DecidableEq α]

/-- All targets meeting one of finitely many additional monomials are bounded by
the common-multiple count, with no genericity hypothesis in this counting step. -/
theorem card_targets_hit_by_labels_le {n s : ℕ} (hn : 0 < n)
    (a : Fin n →₀ ℕ) (ha : a.degree = s)
    (e : α → Fin n →₀ ℕ) (he : ∀ i, (e i).degree = s)
    (E : Finset (Fin n →₀ ℕ)) (hE : ∀ b ∈ E, b.degree = 2*s+1 ∧ a ≤ b)
    (L : Finset α)
    (hit : ∀ b ∈ E, ∃ i ∈ L, e i ≠ a ∧ e i ≤ b) :
    E.card ≤ L.card * (n+s-1).choose s := by
  classical
  let targets : α → Finset (Fin n →₀ ℕ) := fun i =>
    E.filter (fun b => e i ≠ a ∧ e i ≤ b)
  have hsub : E ⊆ L.biUnion targets := by
    intro b hb
    obtain ⟨i,hi,hia,hib⟩ := hit b hb
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨hb,hia,hib⟩⟩
  have hcard : ∀ i ∈ L, (targets i).card ≤ (n+s-1).choose s := by
    intro i _
    by_cases hi : e i = a
    · simp [targets,hi]
    · apply MonomialExpansion.card_common_targets_le hn a (e i) ha (he i) (Ne.symm hi)
      intro b hb
      obtain ⟨hb,hne,hib⟩ := Finset.mem_filter.mp hb
      exact ⟨(hE b hb).1,(hE b hb).2,hib⟩
  exact (Finset.card_le_card hsub).trans
    (Finset.card_biUnion_le_card_mul L targets _ hcard)

/-- The generic mixed-minor condition yields a bound uniform in the lifted
subspace. Every additional monomial must differ from the source monomial. -/
theorem card_deficient_targets_le {n s h : ℕ} (hn : 0 < n)
    (v : α → Fin h → K) (hv : UniversalMixedPosition v)
    (U : Submodule K (Fin h → K))
    (a : Fin n →₀ ℕ) (ha : a.degree = s)
    (e : α → Fin n →₀ ℕ) (he : ∀ i, (e i).degree = s)
    (E : Finset (Fin n →₀ ℕ)) (hE : ∀ b ∈ E, b.degree = 2*s+1 ∧ a ≤ b)
    (sets : (Fin n →₀ ℕ) → Finset α)
    (hsets : ∀ b ∈ E, ∀ i ∈ sets b, e i ≠ a ∧ e i ≤ b)
    (hsize : ∀ b ∈ E, (sets b).card ≤ h)
    (hfail : ∀ b ∈ E, finrank K ↥(U ⊔ blockSpan v (sets b)) <
      min (finrank K U + (sets b).card) h) :
    E.card ≤ (h*2^h) * (n+s-1).choose s := by
  obtain ⟨L,hL,hits⟩ := exists_deficient_hitting_set v hv U sets E hsize hfail
  have hc := card_targets_hit_by_labels_le hn a ha e he E hE L (by
    intro b hb
    obtain ⟨i,hi,hib⟩ := hits b hb
    exact ⟨i,hi,hsets b hb i hib⟩)
  exact hc.trans (Nat.mul_le_mul_right _ hL)

end Froberg.MixedExterior
