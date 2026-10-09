module

public import Froberg.RetainedPrefix
public import Froberg.ProjectedPrefix
public import Froberg.SmallScalarSourceBudget
public import Froberg.ParityProfileScalar

@[expose] public section

/-! The small-degree rows delete just one scalar profile, rather than an
entire parity class. This is the scalar incidence input of Appendix E. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Filter MonomialExpansion
open Quartic.PolynomialBilinearCoordinates
open scoped Topology

theorem eventually_field_uniform_single_profile_scalar_open {d e : ℕ} (hd : 0<d)
    (q : ℕ → ℕ)
    (hbudget : ∀ᶠ n : ℕ in atTop,
      5*(n+e-1).choose e*((n+e-1).choose e+q n)≤2*(n+(e+d)-1).choose (e+d)) :
    ∃ n₀ : ℕ,∀ n≥n₀,∀ (K : Type) [Field K] [Infinite K],∀ S : Finset (Fin n),
      S.card≤Sᶜ.card → Sᶜ.card≤S.card+1 → ∀ j,
      ∃ P : MvPolynomial (Fin (finrank K (Fin (q n) → Forms K n d))) K,
        (∃ Q : Fin (q n) → Forms K n d,eval (coordinates K _ Q) P≠0) ∧
        ∀ Q : Fin (q n) → Forms K n d,eval (coordinates K _ Q) P≠0 →
          Function.Injective (ProjectedPrefix.multiplication (fun α => partialDegree S α≠j) Q e) := by
  obtain ⟨m₀,hm₀⟩ := exists_deleted_bidegree_growth_threshold d e hd
  obtain ⟨n₁,hn₁⟩ := eventually_atTop.mp hbudget
  refine ⟨max (2*m₀+1) n₁,?_⟩
  intro n hn K _ _ S hle hupper j
  have hcard : S.card+Sᶜ.card=n := by simpa using Finset.card_add_card_compl S
  have hm : m₀≤S.card := by omega
  have hnpos : 0<n := by omega
  obtain ⟨P,hP,hgood⟩ := retained_prefix_generic_injective_of_growth
    (K := K) (d := d) (e := e) (r := q n) hnpos S j
    (fun U hU => hm₀ K n S hm hle hupper U hU j) (hn₁ n (by omega))
  refine ⟨P,hP,?_⟩
  intro Q hQ a b hab
  apply hgood Q hQ
  apply Subtype.ext
  exact congrArg Subtype.val hab

/-- All small-degree scalar-product collision rows have their required
single-profile avoidance open, with no further asymptotic hypothesis. -/
theorem eventually_field_uniform_small_single_profile_scalar_open {d R : ℕ}
    (hd : 3≤d) (hd8 : d≤8) (hR : R=4 ∨ R=6 ∨ R=8) (hRd : R≤d)
    (q : ℕ → ℕ)
    (hq : Tendsto (fun n : ℕ => (q n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ)))) :
    ∃ n₀ : ℕ,∀ n≥n₀,∀ (K : Type) [Field K] [Infinite K],∀ S : Finset (Fin n),
      S.card≤Sᶜ.card → Sᶜ.card≤S.card+1 → ∀ j,
      ∃ P : MvPolynomial (Fin (finrank K (Fin (q n) → Forms K n d))) K,
        (∃ Q : Fin (q n) → Forms K n d,eval (coordinates K _ Q) P≠0) ∧
        ∀ Q : Fin (q n) → Forms K n d,eval (coordinates K _ Q) P≠0 →
          Function.Injective (ProjectedPrefix.multiplication (fun α => partialDegree S α≠j) Q (d-R)) :=
  eventually_field_uniform_single_profile_scalar_open (by omega) q
    (eventually_small_scalar_source_budget hd hd8 hR hRd q hq)

theorem eventually_field_uniform_generic_profile_scalar_separation
    {d e : ℕ} (hd : 9≤d) (he : e+4≤d)
    (r : ℕ → ℕ)
    (hr : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d / (d.factorial : ℝ)))) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ (K : Type) [Field K] [Infinite K], ∀ S : Finset (Fin n),
      S.card≤Sᶜ.card → Sᶜ.card≤S.card+1 → ∀ p<2, ∀ j : ℕ,
      ∃ Q : MvPolynomial (Fin (finrank K (Fin (r n) → Forms K n d))) K,
        (∃ f : Fin (r n) → Forms K n d, eval (coordinates K _ f) Q ≠ 0) ∧
        ∀ f : Fin (r n) → Forms K n d, eval (coordinates K _ f) Q ≠ 0 →
          Function.Injective (ProjectedPrefix.multiplication (parityProfileRetained S p j) f e) ∧
          Disjoint (familySpace f * Forms K n e)
            (retainMonomials (K := K) (parityProfileRetained S p j)).ker := by
  obtain ⟨m₀,hm₀⟩ := exists_parity_profile_growth_threshold hd e
  obtain ⟨n₁,hn₁⟩ := eventually_atTop.mp (eventually_profile_scalar_incidence_budget he r hr)
  refine ⟨max (2*m₀+1) n₁,?_⟩
  intro n hn K _ _ S hle hupper p hp j
  have hcard : S.card+Sᶜ.card=n := by simpa using Finset.card_add_card_compl S
  have hm : m₀≤S.card := by omega
  have hnpos : 0<n := by omega
  obtain ⟨Q,hQ,hgood⟩ := ProjectedPrefix.generic_injective_of_growth
    (K := K) (d := d) (e := e) (r := r n) (parityProfileRetained S p j) hnpos 1 4
    (by norm_num) (by
      intro U hU
      simpa only [one_mul] using hm₀ K n S hm hle hupper U hU p hp j)
    (by simpa only [one_mul] using hn₁ n (by omega))
  refine ⟨Q,hQ,?_⟩
  intro f hf
  have h := hgood f hf
  exact ⟨h,ProjectedPrefix.scalar_product_disjoint_kernel _ f h⟩

end Froberg
