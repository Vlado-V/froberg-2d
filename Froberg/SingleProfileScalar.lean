import Froberg.RetainedPrefix
import Froberg.ProjectedPrefix
import Froberg.SmallScalarSourceBudget

/-! The small-degree rows delete just one scalar profile, rather than an
entire parity class. This is the scalar incidence input of Appendix E. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Filter MonomialExpansion
open Quartic.PolynomialBilinearCoordinates
open scoped Topology
variable {K : Type*} [Field K] [Infinite K]

theorem eventually_single_profile_scalar_open {d e : ℕ} (hd : 0<d)
    (q : ℕ → ℕ)
    (hbudget : ∀ᶠ n : ℕ in atTop,
      5*(n+e-1).choose e*((n+e-1).choose e+q n)≤2*(n+(e+d)-1).choose (e+d)) :
    ∃ n₀ : ℕ,∀ n≥n₀,∀ S : Finset (Fin n),
      S.card≤Sᶜ.card → Sᶜ.card≤S.card+1 → ∀ j,
      ∃ P : MvPolynomial (Fin (finrank K (Fin (q n) → Forms K n d))) K,
        (∃ Q : Fin (q n) → Forms K n d,eval (coordinates K _ Q) P≠0) ∧
        ∀ Q : Fin (q n) → Forms K n d,eval (coordinates K _ Q) P≠0 →
          Function.Injective (ProjectedPrefix.multiplication (fun α => partialDegree S α≠j) Q e) := by
  obtain ⟨m₀,hm₀⟩ := exists_deleted_bidegree_growth_threshold d e hd
  obtain ⟨n₁,hn₁⟩ := eventually_atTop.mp hbudget
  refine ⟨max (2*m₀+1) n₁,?_⟩
  intro n hn S hle hupper j
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
theorem eventually_small_single_profile_scalar_open {d R : ℕ}
    (hd : 3≤d) (hd8 : d≤8) (hR : R=4 ∨ R=6 ∨ R=8) (hRd : R≤d)
    (q : ℕ → ℕ)
    (hq : Tendsto (fun n : ℕ => (q n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ)))) :
    ∃ n₀ : ℕ,∀ n≥n₀,∀ S : Finset (Fin n),
      S.card≤Sᶜ.card → Sᶜ.card≤S.card+1 → ∀ j,
      ∃ P : MvPolynomial (Fin (finrank K (Fin (q n) → Forms K n d))) K,
        (∃ Q : Fin (q n) → Forms K n d,eval (coordinates K _ Q) P≠0) ∧
        ∀ Q : Fin (q n) → Forms K n d,eval (coordinates K _ Q) P≠0 →
          Function.Injective (ProjectedPrefix.multiplication (fun α => partialDegree S α≠j) Q (d-R)) :=
  eventually_single_profile_scalar_open (by omega) q
    (eventually_small_scalar_source_budget hd hd8 hR hRd q hq)

end Froberg
