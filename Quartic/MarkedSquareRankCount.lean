module

public import Quartic.MarkedRankEndpoint
public import Quartic.Counts

@[expose] public section

/-! The enlarged response rank supplies the literal marked lower endpoint. -/
noncomputable section
namespace Quartic.MarkedSquareRankCount
open Module
variable {K : Type*} [Field K] {m c q : ℕ}

theorem marked_of_gain (f : Fin (4+(c+q)) → Forms K (3+m) 2)
    (hf : LinearIndependent K f) (ζ : Forms K (3+m) 2) (split response : ℕ)
    (hsplit : (split:ℤ)=Counts.b4 (3+m)-Counts.j m q c)
    (hresponse : Counts.hTotal m q c+1 ≤ (response:ℤ))
    (hgain : split+response ≤ finrank K
      (MarkedRankTransfer.augmented (quadraticMultiplication f) (mulQuadratic ζ ζ)).range) :
    MarkedLowerWitness K (3+m) (4+(c+q)) := by
  apply MarkedRankEndpoint.marked_of_augmented_rank f hf ζ
  have hB : finrank K (koszulSpace f)=(4+(c+q)).choose 2 :=
    (finrank_span_eq_card (koszulVector_linearIndependent f hf)).trans card_generatorPair
  have hker := Submodule.finrank_mono (kernel_contains_koszul f)
  change finrank K (koszulSpace f) ≤ finrank K (quadraticMultiplication f).ker at hker
  have hsum := (quadraticMultiplication f).finrank_range_add_finrank_ker
  rw [hB] at hker
  rw [MarkedRankEndpoint.source_dimension] at hsum
  have he := Counts.transfer_euler_identity m q c
  rw [show m+3=3+m by omega,show q+c+4=4+(c+q) by omega] at he
  unfold Counts.chi Counts.b4 Counts.b2 at he
  unfold Counts.b4 at hsplit
  have hprod : (((4+(c+q))*((3+m)+1).choose 2:ℕ):ℤ)=
      ((4+(c+q):ℕ):ℤ)*(((3+m)+1).choose 2:ℤ) := by push_cast; rfl
  omega

end Quartic.MarkedSquareRankCount
