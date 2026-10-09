module

public import Froberg.ScalarSeparation

@[expose] public section

/-! The full generic scalar-family consequence of the deleted-bidegree estimate. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Filter
open Quartic.PolynomialBilinearCoordinates
open scoped Topology

/-- Families of the manuscript's asymptotic scalar size generically multiply
injectively into the quotient by any one bidegree summand. Their product space
is therefore disjoint from that summand. -/
theorem eventually_uniform_generic_scalar_separation {d : ℕ} (hd : 2 ≤ d)
    (r : ℕ → ℕ)
    (hr : Tendsto (fun n : ℕ => (r n : ℝ) / (n : ℝ) ^ d)
      atTop (𝓝 (criticalRatio d / (d.factorial : ℝ)))) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (K : Type) [Field K] [Infinite K], ∀ S : Finset (Fin n),
      S.card ≤ Sᶜ.card → Sᶜ.card ≤ S.card + 1 → ∀ j : ℕ,
      ∃ P : MvPolynomial (Fin (finrank K (Fin (r n) → Forms K n d))) K,
        (∃ f : Fin (r n) → Forms K n d, eval (coordinates K _ f) P ≠ 0) ∧
        ∀ f : Fin (r n) → Forms K n d, eval (coordinates K _ f) P ≠ 0 →
          Function.Injective (quotientPrefixMultiplication S j f (d - 2)) ∧
          Disjoint (familySpace f * Forms K n (d - 2))
            (deletedBidegreeSpace K S (2 * d - 2) j) := by
  obtain ⟨m₀, hm₀⟩ := exists_deleted_bidegree_growth_threshold d (d - 2) (by omega)
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp (eventually_critical_scalar_incidence_budget hd r hr)
  refine ⟨max (2 * m₀ + 1) n₁, ?_⟩
  intro n hn K _ _ S hle hupper j
  have hcard : S.card + Sᶜ.card = n := by simpa using Finset.card_add_card_compl S
  have hm : m₀ ≤ S.card := by omega
  have hnpos : 0 < n := by omega
  have hc : 5 * (n + (d - 2) - 1).choose (d - 2) *
      ((n + (d - 2) - 1).choose (d - 2) + r n) ≤
      2 * (n + (d - 2 + d) - 1).choose (d - 2 + d) := by
    simpa only [show d - 2 + d = 2 * d - 2 by omega] using hn₁ n (by omega)
  obtain ⟨P, hP, hgood⟩ := retained_prefix_generic_injective_of_growth
    (K := K) (d := d) (e := d - 2) (r := r n) hnpos S j
    (fun U hU => hm₀ K n S hm hle hupper U hU j) hc
  refine ⟨P, hP, ?_⟩
  intro f hf
  have h := hgood f hf
  refine ⟨quotientPrefixMultiplication_injective S j f h, ?_⟩
  simpa only [show d + (d - 2) = 2 * d - 2 by omega] using
    scalar_product_disjoint_deleted_bidegree S j f h

end Froberg
