import Froberg.DeletedBidegreeQuotient
import Froberg.PrefixGrowth

/-! Generic scalar families have no low-degree relation after deleting a
bidegree, once the weighted image bound exceeds the incidence parameter count. -/
noncomputable section
namespace Froberg
open Module MvPolynomial MonomialExpansion
open Quartic.PolynomialBilinearCoordinates
variable {K : Type*} [Field K] {n d e r : ℕ}

abbrev RetainedForms (K : Type*) [Field K] {n : ℕ}
    (S : Finset (Fin n)) (D j : ℕ) :=
  (Forms K n D).map (retainMonomials (fun a => partialDegree S a ≠ j))

def retainDegree (S : Finset (Fin n)) (D j : ℕ) :
    Forms K n D →ₗ[K] RetainedForms K S D j :=
  ((retainMonomials (fun a => partialDegree S a ≠ j)).comp (Forms K n D).subtype).codRestrict
    _ (fun f => ⟨f.val, f.property, rfl⟩)

def retainedPrefixBilinear (S : Finset (Fin n)) (j : ℕ) :
    (Fin r → Forms K n e) →ₗ[K]
      (Fin r → Forms K n d) →ₗ[K] RetainedForms K S (d + e) j where
  toFun a := (retainDegree S (d + e) j).comp (prefixBilinear a)
  map_add' a b := by
    ext q
    simp
  map_smul' c a := by
    ext q
    simp

def retainedPrefixMultiplication (S : Finset (Fin n)) (j : ℕ)
    (f : Fin r → Forms K n d) (e : ℕ) :
    (Fin r → Forms K n e) →ₗ[K] RetainedForms K S (d + e) j :=
  (retainedPrefixBilinear S j).flip f

theorem retainedPrefixMultiplication_val (S : Finset (Fin n)) (j : ℕ)
    (f : Fin r → Forms K n d) (a : Fin r → Forms K n e) :
    (retainedPrefixMultiplication S j f e a).val =
      retainMonomials (fun b => partialDegree S b ≠ j) (prefixMultiplication f e a).val := rfl

def quotientPrefixMultiplication (S : Finset (Fin n)) (j : ℕ)
    (f : Fin r → Forms K n d) (e : ℕ) :
    (Fin r → Forms K n e) →ₗ[K]
      (Poly K n ⧸ deletedBidegreeSpace K S (d + e) j) :=
  (deletedBidegreeSpace K S (d + e) j).mkQ.comp
    ((Forms K n (d + e)).subtype.comp (prefixMultiplication f e))

theorem quotientPrefixMultiplication_injective (S : Finset (Fin n)) (j : ℕ)
    (f : Fin r → Forms K n d)
    (hf : Function.Injective (retainedPrefixMultiplication S j f e)) :
    Function.Injective (quotientPrefixMultiplication S j f e) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  have ha' : (prefixMultiplication f e a).val ∈ deletedBidegreeSpace K S (d + e) j := by
    exact (Submodule.Quotient.mk_eq_zero _).mp ha
  have hz : retainedPrefixMultiplication S j f e a = 0 := by
    apply Subtype.ext
    exact ha'.2
  apply hf
  simpa using hz

theorem scalar_product_disjoint_deleted_bidegree (S : Finset (Fin n)) (j : ℕ)
    (f : Fin r → Forms K n d)
    (hf : Function.Injective (retainedPrefixMultiplication S j f e)) :
    Disjoint (familySpace f * Forms K n e) (deletedBidegreeSpace K S (d + e) j) := by
  apply Submodule.disjoint_def.mpr
  intro p hp hP
  rw [← range_ambient_prefixMultiplication] at hp
  obtain ⟨a, rfl⟩ := hp
  have hz : retainedPrefixMultiplication S j f e a = 0 := by
    apply Subtype.ext
    exact hP.2
  have ha : a = 0 := hf (by simpa using hz)
  simp [ha]

theorem retainedPrefixBilinear_rank (S : Finset (Fin n)) (j : ℕ)
    (a : Fin r → Forms K n e) :
    finrank K (retainedPrefixBilinear (d := d) S j a).range =
      finrank K ((familySpace a * Forms K n d).map (retainMonomials (fun b => partialDegree S b ≠ j))) := by
  let L : Poly K n →ₗ[K] Poly K n := retainMonomials (fun b => partialDegree S b ≠ j)
  have he : (Forms K n (d + e)).subtype.comp (prefixBilinear a) =
      (Forms K n (e + d)).subtype.comp (prefixMultiplication a d) := by
    ext q
    simp [prefixBilinear, prefixIncidenceFiber_val, prefixMultiplication_val, mul_comm]
  have hbase : ((Forms K n (d + e)).subtype.comp (prefixBilinear a)).range =
      familySpace a * Forms K n d := by
    rw [he, range_ambient_prefixMultiplication]
  have hr : (retainedPrefixBilinear (d := d) S j a).range.map
        (RetainedForms K S (d + e) j).subtype = (familySpace a * Forms K n d).map L := by
    rw [← LinearMap.range_comp]
    change (L.comp ((Forms K n (d + e)).subtype.comp (prefixBilinear a))).range = _
    rw [LinearMap.range_comp, hbase]
  have hh := congrArg (fun U : Submodule K (Poly K n) => finrank K U) hr
  rw [Submodule.finrank_map_subtype_eq] at hh
  exact hh

/-- A numerical strict surplus over the tuple-chart dimension gives a nonempty
principal open of families whose projected multiplication is injective. -/
theorem retained_prefix_generic_injective_of_growth [Infinite K]
    (hn : 0 < n) (S : Finset (Fin n)) (j : ℕ)
    (hgrowth : ∀ U : Submodule K (Poly K n), U ≤ Forms K n e →
      2 * (n + (e + d) - 1).choose (e + d) * finrank K U ≤
        5 * (n + e - 1).choose e *
          finrank K ((U * Forms K n d).map (retainMonomials (fun b => partialDegree S b ≠ j))))
    (hcount : 5 * (n + e - 1).choose e * ((n + e - 1).choose e + r) ≤
      2 * (n + (e + d) - 1).choose (e + d)) :
    ∃ P : MvPolynomial (Fin (finrank K (Fin r → Forms K n d))) K,
      (∃ f : Fin r → Forms K n d, eval (coordinates K _ f) P ≠ 0) ∧
      ∀ f : Fin r → Forms K n d, eval (coordinates K _ f) P ≠ 0 →
        Function.Injective (retainedPrefixMultiplication S j f e) := by
  apply Quartic.BilinearGeneric.generic_injective_actual (retainedPrefixBilinear S j)
  intro a ha
  dsimp only
  rw [finrank_forms K n e hn, retainedPrefixBilinear_rank]
  let N := (n + e - 1).choose e
  let k := finrank K (Submodule.span K (Set.range a))
  have hN : 0 < N := monomial_count_pos hn e
  have hg := hgrowth (familySpace a) (familySpace_homogeneous a)
  rw [finrank_familySpace] at hg
  have hk : k * (N - k) + r * k ≤ k * (N + r) := by
    nlinarith [Nat.mul_le_mul_left k (Nat.sub_le N k)]
  have h : 5 * N * (k * (N - k) + r * k) ≤
      5 * N * finrank K ((familySpace a * Forms K n d).map
        (retainMonomials (fun b => partialDegree S b ≠ j))) := by
    calc
      _ ≤ 5 * N * (k * (N + r)) := Nat.mul_le_mul_left _ hk
      _ = (5 * N * (N + r)) * k := by ring
      _ ≤ (2 * (n + (e + d) - 1).choose (e + d)) * k := Nat.mul_le_mul_right k hcount
      _ ≤ _ := hg
  exact Nat.le_of_mul_le_mul_left h (by positivity)

end Froberg
