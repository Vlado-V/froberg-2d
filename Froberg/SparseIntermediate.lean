import Froberg.IntermediateScalar
import Froberg.OuterGeneric

/-! An actual sparse new-layer family with generically injective common
scalar action, under the manuscript's strict capacity inequality. -/
noncomputable section
namespace Froberg.OuterInjection
open Module MvPolynomial Filter
open Quartic.PolynomialBilinearCoordinates Quartic.HomogeneousCoefficientCoordinates
open scoped Topology
variable {K : Type*} [Field K] [Infinite K]

/-- All degree-s monomials receive b genuine vector labels. A single family
has full polynomial injection and a nonempty scalar-parameter open in the
actual quotient, once the variable count is large enough. -/
theorem eventually_sparse_intermediate_family {s d h b : ℕ}
    (hs : s<d) (hh : 0<h) (hcap : b*(s+d).choose s≤h)
    (q : ℕ → ℕ)
    (hq : Tendsto (fun n : ℕ => (q n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ))))
    (hgap : (b*(s+d).choose s : ℕ)+(h : ℝ)*((s+d).choose s : ℝ)*criticalRatio d<h) :
    ∃ n₀ : ℕ, ∀ n≥n₀,
      ∃ v : Labels b n s → Fin h → K,
        (∀ S : Finset (Labels b n s), S.card≤h → LinearIndependent K (fun i : S => v i.val)) ∧
        MixedExterior.UniversalMixedPosition v ∧
        (∀ c≤d, Function.Injective (AttachedMultiplication.multiplication (d := c) (coreExponent 0) v)) ∧
        ∃ P : MvPolynomial (Fin (finrank K (Fin (q n) → Forms K n d))) K,
          (∃ Q : Fin (q n) → Forms K n d, eval (coordinates K _ Q) P ≠ 0) ∧
          ∀ Q : Fin (q n) → Forms K n d, eval (coordinates K _ Q) P ≠ 0 →
            Function.Injective (BilinearScalarFamily.multiplication
              (AttachedMultiplication.quotientMultiply (d := d) (coreExponent 0) v (coreExponent_degree 0)) Q) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_intermediate_scalar_budget hs hcap q hq hgap)
  refine ⟨max 1 N,?_⟩
  intro n hn
  have hnpos : 0<n := by omega
  obtain ⟨v,hv,hm,hi⟩ := exists_generic_outer_vectors (K := K) b n 0 s d h hcap
  refine ⟨v,hv,hm,hi,?_⟩
  apply AttachedMultiplication.intermediate_scalar_injective_of_budget hnpos hh
    (coreExponent 0) v (coreExponent_degree 0) hv hm hcap
  · intro β
    have hc := card_target_labels_le (k := b) (a := n) (s := s) 0 β.val
    rw [β.property] at hc
    simpa only [AttachedMultiplication.labelsBelow,Fintype.card_subtype] using hc
  · exact hN n (by omega)

end Froberg.OuterInjection
