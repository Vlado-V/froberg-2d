module

public import Quartic.EndpointReduction

@[expose] public section

/-! A lower endpoint witness retaining the square needed in characteristic two. -/
noncomputable section
namespace Quartic

/-- An independent quadratic family with only Koszul relations and a quadratic
whose square survives in the degree-four quotient by that same family. -/
def MarkedLowerWitness (K : Type*) [Field K] (n r : ℕ) : Prop :=
  ∃ q : Fin r → Forms K n 2,
    LinearIndependent K q ∧
    LinearMap.ker (quadraticMultiplication q) ≤ koszulSpace q ∧
    ∃ ζ : Forms K n 2, mulQuadratic ζ ζ ∉ LinearMap.range (quadraticMultiplication q)

theorem MarkedLowerWitness.noHomology {K : Type*} [Field K] {n r : ℕ}
    (h : MarkedLowerWitness K n r) : EndpointReduction.NoHomologyWitness K n r := by
  obtain ⟨q, hq, he, _⟩ := h
  exact ⟨q, hq, he⟩

theorem MarkedLowerWitness.witness {K : Type*} [Field K] {n r : ℕ}
    (h : MarkedLowerWitness K n r) : QuarticWitness K n r :=
  EndpointReduction.noHomology_implies_witness h.noHomology

/-- The marked family itself has the expected quotient dimension. -/
theorem MarkedLowerWitness.expected {K : Type*} [Field K] {n r : ℕ}
    (h : MarkedLowerWitness K n r) :
    ∃ q : Fin r → Forms K n 2,
      LinearIndependent K q ∧
      Module.finrank K (QuarticQuotient K n
        (Submodule.span K (Set.range (fun i => (q i).val)))) = expectedDimension n r ∧
      ∃ ζ : Forms K n 2, mulQuadratic ζ ζ ∉ LinearMap.range (quadraticMultiplication q) := by
  obtain ⟨q, hq, he, hs⟩ := h
  refine ⟨q, hq, ?_, hs⟩
  apply (expected_quotient_iff_homology_or_quotient_zero q hq).mpr
  left
  have heq : koszulSpace q = LinearMap.ker (quadraticMultiplication q) :=
    le_antisymm (kernel_contains_koszul q) he
  have hdim : Module.finrank K (LinearMap.ker (quadraticMultiplication q)) = r.choose 2 := by
    rw [← heq]
    exact (finrank_span_eq_card (koszulVector_linearIndependent q hq)).trans card_generatorPair
  have hhom := homology_add_pairs q hq
  omega

end Quartic
