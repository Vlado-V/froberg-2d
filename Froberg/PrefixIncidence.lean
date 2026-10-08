import Froberg.Prefix
import Quartic.BilinearGeneric

/-!
# The incidence criterion for prefix injectivity

Connects the arbitrary-degree polynomial multiplication maps to the proved
projective rank-stratum avoidance engine from the earlier Quartic project.
The remaining hypothesis is an explicit bound on the Hilbert function of
every coefficient ideal. This file does not assert that bound without proof.
-/

noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type*} [Field K] {n d e r : ℕ}

/-- The prefix incidence equation, bilinear in relations and generators. -/
def prefixBilinear : (Fin r → Forms K n e) →ₗ[K]
    (Fin r → Forms K n d) →ₗ[K] Forms K n (d + e) where
  toFun := prefixIncidenceFiber
  map_add' a b := by
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    simp [prefixIncidenceFiber_val, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    simp [prefixIncidenceFiber_val, Finset.smul_sum]

theorem prefixBilinear_flip (q : Fin r → Forms K n d) :
    prefixBilinear.flip q = prefixMultiplication q e := by
  ext a
  rfl

/-- The rank of the fixed-relation equation is the complement of the Hilbert
function of its coefficient ideal. -/
theorem prefix_incidence_rank_add_hilbert (hn : 0 < n)
    (a : Fin r → Forms K n e) :
    finrank K (prefixIncidenceFiber (d := d) a).range +
      hilbertFunction (familySpace a) (d + e) =
        (n + (d + e) - 1).choose (d + e) := by
  have h₁ := prefix_incidence_fiber_dimension (d := d) hn a
  have h₂ := (prefixIncidenceFiber (d := d) a).finrank_range_add_finrank_ker
  rw [Module.finrank_pi_fintype, finrank_forms K n d hn] at h₂
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_id] at h₂
  omega

/-- The exact projective incidence dimension criterion gives a genuine
injective multiplication witness, over every infinite coefficient field. -/
theorem exists_prefix_injective_of_hilbert_bound [Infinite K] (hn : 0 < n)
    (hbound : ∀ a : Fin r → Forms K n e, a ≠ 0 →
      let s := finrank K (Submodule.span K (Set.range a))
      s * ((n + e - 1).choose e - s) + r * s +
        hilbertFunction (familySpace a) (d + e) ≤
          (n + (d + e) - 1).choose (d + e)) :
    ∃ q : Fin r → Forms K n d, Function.Injective (prefixMultiplication q e) := by
  have hdim : ∀ a : Fin r → Forms K n e, a ≠ 0 →
      let s := finrank K (Submodule.span K (Set.range a))
      s * (finrank K (Forms K n e) - s) + r * s ≤
        finrank K (prefixBilinear (d := d) a).range := by
    intro a ha
    dsimp only
    rw [finrank_forms K n e hn]
    have h := hbound a ha
    have hi := prefix_incidence_rank_add_hilbert (d := d) hn a
    change finrank K (prefixIncidenceFiber (d := d) a).range + _ = _ at hi
    change _ ≤ finrank K (prefixIncidenceFiber (d := d) a).range
    dsimp only at h
    omega
  obtain ⟨q, hq⟩ := Quartic.BilinearGeneric.exists_injective
    (prefixBilinear (K := K) (n := n) (d := d) (e := e) (r := r)) hdim
  exact ⟨q, by rwa [prefixBilinear_flip] at hq⟩

/-- The incidence Hilbert bound yields a nonempty principal open attaining the
universal quotient-dimension lower bound. -/
theorem prefix_principal_open_of_hilbert_bound [Infinite K] (hn : 0 < n)
    (hbound : ∀ a : Fin r → Forms K n e, a ≠ 0 →
      let s := finrank K (Submodule.span K (Set.range a))
      s * ((n + e - 1).choose e - s) + r * s +
        hilbertFunction (familySpace a) (d + e) ≤
          (n + (d + e) - 1).choose (d + e)) :
    ∃ D : MvPolynomial (CoefficientIndex n d r) K,
      (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
        hilbertFunction (coefficientSpace K n d r a) (d + e) =
          (n + (d + e) - 1).choose (d + e) - r * (n + e - 1).choose e := by
  obtain ⟨q, hq⟩ := exists_prefix_injective_of_hilbert_bound hn hbound
  let a₀ := coefficientCoordinates (K := K) (n := n) (d := d) (r := r) q
  have hq₀ : coefficientForms K n d r a₀ = q := coefficientCoordinates.symm_apply_apply q
  have h₀ : hilbertFunction (coefficientSpace K n d r a₀) (d + e) =
      (n + (d + e) - 1).choose (d + e) - r * (n + e - 1).choose e := by
    change hilbertFunction (familySpace (coefficientForms K n d r a₀)) (d + e) = _
    rw [hq₀]
    exact prefix_hilbert_of_injective hn q hq
  obtain ⟨D, hD, hgood⟩ := prefix_lower_bound_principal_open hn a₀ h₀
  exact ⟨D, ⟨a₀, hD⟩, hgood⟩

/-- The normalized Hilbert-growth estimate in the BDL argument implies the
rank-stratum bound for every generator count on the injective side. -/
theorem prefix_rank_budget_of_normalized_bound
    {N M r s H : ℕ} (hN : 0 < N) (hs : s ≤ N) (hr : r * N ≤ M)
    (hH : N * (H + s * (N - s)) ≤ (N - s) * M) :
    s * (N - s) + r * s + H ≤ M := by
  have he : s + (N - s) = N := Nat.add_sub_of_le hs
  have hcalc : N * (s * (N - s) + r * s + H) ≤ N * M := calc
    _ = N * (H + s * (N - s)) + s * (r * N) := by ring
    _ ≤ (N - s) * M + s * M := Nat.add_le_add hH (Nat.mul_le_mul_left s hr)
    _ = N * M := by nlinarith
  nlinarith

/-- A uniform Hilbert-growth bound for coefficient ideals supplies the whole
injective range of the lower-degree multiplication problem. -/
theorem exists_prefix_injective_of_normalized_hilbert_bound [Infinite K]
    (hn : 0 < n) (hr : r * (n + e - 1).choose e ≤
      (n + (d + e) - 1).choose (d + e))
    (hbound : ∀ a : Fin r → Forms K n e, a ≠ 0 →
      let s := finrank K (Submodule.span K (Set.range a))
      (n + e - 1).choose e *
          (hilbertFunction (familySpace a) (d + e) + s * ((n + e - 1).choose e - s)) ≤
        ((n + e - 1).choose e - s) * (n + (d + e) - 1).choose (d + e)) :
    ∃ q : Fin r → Forms K n d, Function.Injective (prefixMultiplication q e) := by
  apply exists_prefix_injective_of_hilbert_bound hn
  intro a ha
  dsimp only
  have hs : finrank K (Submodule.span K (Set.range a)) ≤ (n + e - 1).choose e := by
    simpa only [finrank_forms K n e hn] using
      Submodule.finrank_le (Submodule.span K (Set.range a))
  exact prefix_rank_budget_of_normalized_bound (monomial_count_pos hn e) hs hr (hbound a ha)

end Froberg
