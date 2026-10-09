module

public import Quartic.MarkedRankTransfer
public import Quartic.MarkedLowerWitness

@[expose] public section

/-! An augmented multiplication rank bound certifies the actual lower endpoint
and a surviving square for that same independent quadratic family. -/
noncomputable section
namespace Quartic.MarkedRankEndpoint
open Module MarkedRankTransfer
variable {K : Type*} [Field K] {n r : ℕ}

theorem source_dimension :
    finrank K (Fin r → Forms K n 2)=r*(n+1).choose 2 := by
  simp [Module.finrank_pi_fintype,finrank_quadrics]

theorem multiplication_rank_le (q : Fin r → Forms K n 2) (hq : LinearIndependent K q) :
    finrank K (quadraticMultiplication q).range≤r*(n+1).choose 2-r.choose 2 := by
  have hB : finrank K (koszulSpace q)=r.choose 2 :=
    (finrank_span_eq_card (koszulVector_linearIndependent q hq)).trans card_generatorPair
  have hker := Submodule.finrank_mono (kernel_contains_koszul q)
  change finrank K (koszulSpace q)≤finrank K (quadraticMultiplication q).ker at hker
  have hsum := (quadraticMultiplication q).finrank_range_add_finrank_ker
  rw [hB] at hker
  rw [source_dimension] at hsum
  omega

theorem kernel_le_of_rank (q : Fin r → Forms K n 2) (hq : LinearIndependent K q)
    (hrank : r*(n+1).choose 2-r.choose 2≤finrank K (quadraticMultiplication q).range) :
    (quadraticMultiplication q).ker≤koszulSpace q := by
  have hB : finrank K (koszulSpace q)=r.choose 2 :=
    (finrank_span_eq_card (koszulVector_linearIndependent q hq)).trans card_generatorPair
  have hker := Submodule.finrank_mono (kernel_contains_koszul q)
  change finrank K (koszulSpace q)≤finrank K (quadraticMultiplication q).ker at hker
  have hsum := (quadraticMultiplication q).finrank_range_add_finrank_ker
  rw [hB] at hker
  rw [source_dimension] at hsum
  have heq : koszulSpace q=(quadraticMultiplication q).ker := by
    apply Submodule.eq_of_le_of_finrank_eq (kernel_contains_koszul q)
    change finrank K (koszulSpace q)=finrank K (quadraticMultiplication q).ker
    rw [hB]
    omega
  exact heq.ge

theorem exact_and_square_survives (q : Fin r → Forms K n 2)
    (hq : LinearIndependent K q) (ζ : Forms K n 2)
    (haug : r*(n+1).choose 2-r.choose 2+1≤
      finrank K (augmented (quadraticMultiplication q) (mulQuadratic ζ ζ)).range) :
    (quadraticMultiplication q).ker≤koszulSpace q ∧
      mulQuadratic ζ ζ∉(quadraticMultiplication q).range := by
  have h := rank_and_survival (quadraticMultiplication q) (mulQuadratic ζ ζ)
    (r*(n+1).choose 2-r.choose 2) (multiplication_rank_le q hq) haug
  exact ⟨kernel_le_of_rank q hq h.1.ge,h.2.1⟩

theorem marked_of_augmented_rank (q : Fin r → Forms K n 2)
    (hq : LinearIndependent K q) (ζ : Forms K n 2)
    (haug : r*(n+1).choose 2-r.choose 2+1≤
      finrank K (augmented (quadraticMultiplication q) (mulQuadratic ζ ζ)).range) :
    MarkedLowerWitness K n r := by
  obtain ⟨he,hs⟩ := exact_and_square_survives q hq ζ haug
  exact ⟨q,hq,he,ζ,hs⟩

end Quartic.MarkedRankEndpoint
