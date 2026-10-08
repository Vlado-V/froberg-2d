import Froberg.DeletedBidegree

/-! The coordinate-retention formulation of Appendix C.1 equals the dimension
of the image in the quotient by the deleted homogeneous bidegree summand. -/
noncomputable section
namespace Froberg
open Module MvPolynomial MonomialExpansion
variable {K : Type*} [Field K] {n D d e : ℕ}

def deletedBidegreeSpace (K : Type*) [Field K] {n : ℕ}
    (S : Finset (Fin n)) (D j : ℕ) : Submodule K (Poly K n) :=
  Forms K n D ⊓ (retainMonomials (fun a => partialDegree S a ≠ j)).ker

theorem mem_deletedBidegreeSpace_iff (S : Finset (Fin n)) (j : ℕ) (f : Poly K n) :
    f ∈ deletedBidegreeSpace K S D j ↔
      f ∈ Forms K n D ∧ ∀ a, partialDegree S a ≠ j → f.coeff a = 0 := by
  change (f ∈ Forms K n D ∧ retainMonomials (fun a => partialDegree S a ≠ j) f = 0) ↔ _
  constructor
  · rintro ⟨hf, hz⟩
    refine ⟨hf, ?_⟩
    intro a ha
    have h := congrArg (fun g : Poly K n => g.coeff a) hz
    simpa [coeff_retainMonomials, ha] using h
  · rintro ⟨hf, hc⟩
    refine ⟨hf, ?_⟩
    ext a
    by_cases ha : partialDegree S a ≠ j
    · simpa [coeff_retainMonomials, ha] using hc a ha
    · simp [coeff_retainMonomials, ha]

theorem finrank_retained_eq_quotient_image (S : Finset (Fin n)) (j : ℕ)
    (V : Submodule K (Poly K n)) (hV : V ≤ Forms K n D) :
    finrank K (V.map (retainMonomials (fun a => partialDegree S a ≠ j))) =
      finrank K (V.map (deletedBidegreeSpace K S D j).mkQ) := by
  let : FiniteDimensional K V := Submodule.finiteDimensional_of_le hV
  let L : Poly K n →ₗ[K] Poly K n := retainMonomials (fun a => partialDegree S a ≠ j)
  let Q := (deletedBidegreeSpace K S D j).mkQ
  have hk : (L.comp V.subtype).ker = (Q.comp V.subtype).ker := by
    rw [LinearMap.ker_comp, LinearMap.ker_comp]
    change L.ker.comap V.subtype = ((deletedBidegreeSpace K S D j).mkQ.ker).comap V.subtype
    rw [Submodule.ker_mkQ]
    change L.ker.comap V.subtype = (Forms K n D ⊓ L.ker).comap V.subtype
    ext x
    change L x.val = 0 ↔ x.val ∈ Forms K n D ∧ L x.val = 0
    exact ⟨fun h => ⟨hV x.property, h⟩, fun h => h.2⟩
  have h₁ := (L.comp V.subtype).finrank_range_add_finrank_ker
  have h₂ := (Q.comp V.subtype).finrank_range_add_finrank_ker
  rw [LinearMap.range_comp, Submodule.range_subtype] at h₁ h₂
  rw [hk] at h₁
  change finrank K (V.map L) = finrank K (V.map Q)
  omega

/-- Appendix C.1 as the actual image dimension in the quotient by one full
homogeneous bidegree summand. -/
theorem deleted_bidegree_quotient_lemma (d : ℕ) (hd : 2 ≤ d) :
    ∃ m₀ : ℕ, ∀ (K : Type*) [Field K] (n : ℕ) (S : Finset (Fin n)),
      m₀ ≤ S.card → S.card ≤ Sᶜ.card → Sᶜ.card ≤ S.card + 1 →
      ∀ (U : Submodule K (Poly K n)), U ≤ Forms K n (d - 2) → ∀ j : ℕ,
        2 * (n + (2 * d - 2) - 1).choose (2 * d - 2) * finrank K U ≤
          5 * (n + (d - 2) - 1).choose (d - 2) * finrank K
            ((U * Forms K n d).map (deletedBidegreeSpace K S (2 * d - 2) j).mkQ) := by
  obtain ⟨m₀, hm₀⟩ := deleted_bidegree_lemma d hd
  refine ⟨m₀, ?_⟩
  intro K _ n S hm hle hupper U hU j
  have h := hm₀ K n S hm hle hupper U hU j
  have hprod : U * Forms K n d ≤ Forms K n (2 * d - 2) := by
    have h := (mul_le_mul_left hU (Forms K n d)).trans (MvPolynomial.homogeneousSubmodule_mul (d - 2) d)
    simpa only [show d - 2 + d = 2 * d - 2 by omega] using h
  rwa [finrank_retained_eq_quotient_image S j (U * Forms K n d) hprod] at h

end Froberg
