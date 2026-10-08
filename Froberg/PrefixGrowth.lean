import Froberg.InitialSubspace
import Froberg.MonomialExpansionBound
import Froberg.PrefixIncidence
import Mathlib.Data.Finsupp.MonomialOrder.DegLex

/-! Uniform homogeneous-subspace growth obtained by weighted monomial expansion.
This supplies the coefficient-ideal estimate in prefix incidence without an
assumed Macaulay growth theorem. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Finset MonomialExpansion
variable {K : Type*} [Field K] {n e d r : ℕ}

/-- Strengthened normalized growth of every homogeneous polynomial subspace. -/
theorem homogeneous_subspace_growth (hn : 0 < n) (hed : e < d)
    (hlarge : (e + d).choose e * ((e + d).choose e * d.choose e) ≤ n)
    (U : Submodule K (Poly K n)) (hU : U ≤ Forms K n e) :
    (n + (e + d) - 1).choose (e + d) * finrank K U +
      (n + e - 1).choose e * finrank K U * ((n + e - 1).choose e - finrank K U) ≤
      (n + e - 1).choose e * finrank K (U * Forms K n d) := by
  classical
  let m : MonomialOrder (Fin n) := MonomialOrder.degLex
  let A : Finset (Degree n e) := univ.filter
    (fun a => a.val ∈ initialDegrees (d := e) m U)
  have hA : A.card = finrank K U := by
    rw [← card_initialDegrees m U hU]
    apply Finset.card_bij (fun a _ => a.val)
    · intro a ha
      exact (mem_filter.mp ha).2
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro a ha
      refine ⟨⟨a, mem_exponents.mpr (initialDegrees_degree m U ha)⟩, ?_, rfl⟩
      exact mem_filter.mpr ⟨mem_univ _, ha⟩
  let B : Finset (Fin n →₀ ℕ) := (shadow d A).image Subtype.val
  have hBcard : B.card = (shadow d A).card :=
    Finset.card_image_iff.mpr (fun _ _ _ _ h => Subtype.ext h)
  have hB : B.card ≤ finrank K (U * Forms K n d) := by
    apply card_le_finrank_product_of_initial_factors m U hU B
    intro b hb
    obtain ⟨β, hβ, rfl⟩ := mem_image.mp hb
    obtain ⟨α, hα, hαβ⟩ := (mem_filter.mp hβ).2
    refine ⟨α.val, (mem_filter.mp hα).2, β.val - α.val, ?_, ?_⟩
    · have h := congrArg Finsupp.degree (tsub_add_cancel_of_le hαβ)
      rw [map_add, degree_val, degree_val] at h
      omega
    · exact add_tsub_cancel_of_le hαβ
  have h := shadow_expansion_of_large_variables hn hed hlarge A
  rw [hA] at h
  exact h.trans (Nat.mul_le_mul_left _ (hBcard ▸ hB))

/-- The polynomial span and the span inside the homogeneous piece have the same dimension. -/
theorem finrank_familySpace (a : Fin r → Forms K n e) :
    finrank K (familySpace a) = finrank K (Submodule.span K (Set.range a)) := by
  have he : familySpace a =
      (Submodule.span K (Set.range a)).map (Forms K n e).subtype := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [he, Submodule.finrank_map_subtype_eq]

/-- Exact codimension of the coefficient-ideal product piece. -/
theorem prefix_hilbert_add_product_rank (hn : 0 < n) (a : Fin r → Forms K n e) :
    hilbertFunction (familySpace a) (e + d) + finrank K (familySpace a * Forms K n d) =
      (n + (e + d) - 1).choose (e + d) := by
  have he := range_ambient_prefixMultiplication (e := d) a
  rw [LinearMap.range_comp] at he
  have hh := congrArg (fun S : Submodule K (Poly K n) => finrank K S) he
  rw [Submodule.finrank_map_subtype_eq] at hh
  rw [← hh]
  exact prefix_hilbert_add_rank hn a

/-- The actual coefficient ideal satisfies the uniform normalized Hilbert bound. -/
theorem prefix_normalized_hilbert_bound (hn : 0 < n) (hed : e < d)
    (hlarge : (e + d).choose e * ((e + d).choose e * d.choose e) ≤ n)
    (a : Fin r → Forms K n e) :
    let s := finrank K (Submodule.span K (Set.range a))
    (n + e - 1).choose e *
        (hilbertFunction (familySpace a) (d + e) + s * ((n + e - 1).choose e - s)) ≤
      ((n + e - 1).choose e - s) * (n + (d + e) - 1).choose (d + e) := by
  dsimp only
  have hg := homogeneous_subspace_growth hn hed hlarge (familySpace a) (familySpace_homogeneous a)
  rw [finrank_familySpace] at hg
  have hs : finrank K (Submodule.span K (Set.range a)) ≤ (n + e - 1).choose e := by
    simpa only [finrank_forms K n e hn] using
      Submodule.finrank_le (Submodule.span K (Set.range a))
  have hh := prefix_hilbert_add_product_rank (d := d) hn a
  rw [Nat.add_comm e d] at hg hh
  have he := Nat.sub_add_cancel hs
  have hhN := congrArg (fun t : ℕ => (n + e - 1).choose e * t) hh
  have heM := congrArg (fun t : ℕ => t * (n + (d + e) - 1).choose (d + e)) he
  nlinarith

/-- Actual generic injectivity below the endpoint, uniformly in generator count. -/
theorem exists_prefix_injective_of_large_variables [Infinite K] (hn : 0 < n) (hed : e < d)
    (hlarge : (e + d).choose e * ((e + d).choose e * d.choose e) ≤ n)
    (hr : r * (n + e - 1).choose e ≤ (n + (d + e) - 1).choose (d + e)) :
    ∃ q : Fin r → Forms K n d, Function.Injective (prefixMultiplication q e) := by
  apply exists_prefix_injective_of_normalized_hilbert_bound hn hr
  intro a _
  exact prefix_normalized_hilbert_bound hn hed hlarge a

end Froberg
