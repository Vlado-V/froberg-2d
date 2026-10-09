module

public import Froberg.InitialSubspace
public import Froberg.MonomialExpansionBound
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex

@[expose] public section

/-! Ordinary normalized multiplication growth, valid in every pair of degrees. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Finset MonomialExpansion
variable {K : Type*} [Field K] {n e d : ℕ}

 theorem normalized_monomial_shadow (hn : 0 < n) (A : Finset (Degree n e)) :
    (n+(e+d)-1).choose (e+d)*A.card ≤ (n+e-1).choose e*(shadow d A).card := by
  have htotal := weighted_total
    (fun (b : Degree n (e+d)) (a : Degree n e) => weight b.val a.val)
    ((e+d).choose e) ((n+e+d-1).choose d) weighted_row (weighted_column hn)
  simp only [card_degree] at htotal
  have hcut := weighted_shadow_cut (d := d) hn A
  have hc : 0 < (e+d).choose e := Nat.choose_pos (Nat.le_add_right _ _)
  have hmul := Nat.mul_le_mul_left ((n+e-1).choose e) hcut
  have he : (n+e-1).choose e * ((n+e+d-1).choose d*A.card) =
      (e+d).choose e*((n+(e+d)-1).choose (e+d)*A.card) := by
    rw [← mul_assoc,htotal]
    ring
  nlinarith

theorem homogeneous_normalized_growth (hn : 0 < n)
    (U : Submodule K (Poly K n)) (hU : U ≤ Forms K n e) :
    (n + (e + d) - 1).choose (e + d) * finrank K U ≤
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
  have h := normalized_monomial_shadow (d := d) hn A
  rw [hA] at h
  exact h.trans (Nat.mul_le_mul_left _ (hBcard ▸ hB))

end Froberg
