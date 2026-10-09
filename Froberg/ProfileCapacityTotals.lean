module

public import Froberg.FiniteMonomialTransport
public import Froberg.MonomialFiberEquivalences

@[expose] public section

/-! Exact identities between total monomial capacities and the finite
profile totals used to normalize the transport. -/
noncomputable section
set_option maxHeartbeats 800000
namespace Froberg
open Finset MonomialExpansion OuterInjection

lemma source_capacity_at_exponent (H : ℝ) {a z s : ℕ}
    (α : Σ i, SourceMonomialFiber a z s i) :
    (H - if (corePart (sourceExponent α).val).degree = s then 1 else 0) =
      profileSourceCapacity H α.1 := by
  rw [sourceExponent_core_degree]
  rcases α with ⟨i, α⟩
  cases i with
  | none => simp [profileSourceIndex, profileSourceCapacity]
  | some i => simp [profileSourceIndex, profileSourceCapacity, ne_of_lt i.isLt]

lemma source_capacity_total (H : ℝ) (a z s : ℕ) :
    (∑ α : Degree (a + z) s, (H - if (corePart α.val).degree = s then 1 else 0)) =
      ∑ i, finiteSourceProfile H s a z i := by
  classical
  rw [← (sourceMonomialEquiv a z s).sum_comp
    (fun α => (H - if (corePart α.val).degree = s then 1 else 0))]
  change (∑ α : Σ i, SourceMonomialFiber a z s i,
    (H - if (corePart (sourceExponent α).val).degree = s then 1 else 0)) = _
  simp only [source_capacity_at_exponent, Fintype.sum_sigma, sum_const, card_univ,
    nsmul_eq_mul, finiteSourceProfile_eq_card]
  apply sum_congr rfl
  intro i _
  ring

lemma target_capacity_at_exponent {a z s : ℕ}
    (β : Σ j, TargetMonomialFiber a z s j) :
    ((((2 * s + 1).choose s : ℕ) : ℝ) - ((corePart (targetExponent β).val.val).degree.choose s : ℝ)) =
      profileTargetCapacity s β.1 := by
  simp only [targetExponent, corePart_joinParts, degree_val, profileTargetCapacity]

lemma target_capacity_total (a z s : ℕ) :
    (∑ β : Degree (a + z) (2 * s + 1),
      ((((2 * s + 1).choose s : ℕ) : ℝ) - ((corePart β.val).degree.choose s : ℝ))) =
      ∑ j, finiteTargetProfile s a z j := by
  classical
  let f : Degree (a + z) (2 * s + 1) → ℝ := fun β =>
    (((2 * s + 1).choose s : ℕ) : ℝ) - ((corePart β.val).degree.choose s : ℝ)
  have hzero : ∀ β : Degree (a + z) (2 * s + 1),
      ¬(corePart β.val).degree < 2 * s + 1 → f β = 0 := by
    intro β hβ
    have hle := corePart_le_degree β.val
    rw [degree_val] at hle
    have heq : (corePart β.val).degree = 2 * s + 1 := by omega
    simp [f, heq]
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun β : Degree (a + z) (2 * s + 1) => (corePart β.val).degree < 2 * s + 1) f
  have hother : (∑ β : {β : Degree (a + z) (2 * s + 1) //
      ¬(corePart β.val).degree < 2 * s + 1}, f β.val) = 0 :=
    sum_eq_zero fun β _ => hzero β.val β.property
  rw [hother, add_zero] at hsplit
  change (∑ β, f β) = _
  rw [← hsplit]
  change (∑ β : PositiveTargetMonomial a z s, f β.val) = _
  rw [← (targetMonomialEquiv a z s).sum_comp (fun β => f β.val)]
  change (∑ β : Σ j, TargetMonomialFiber a z s j,
    ((((2 * s + 1).choose s : ℕ) : ℝ) - ((corePart (targetExponent β).val.val).degree.choose s : ℝ))) = _
  simp only [target_capacity_at_exponent, Fintype.sum_sigma, sum_const, card_univ,
    nsmul_eq_mul, finiteTargetProfile_eq_card]
  apply sum_congr rfl
  intro j _
  ring

end Froberg
