module

public import Froberg.PreparedAllEvenCounts
public import Froberg.LocalComparison

@[expose] public section

/-! Exact final and temporary cardinalities in Section 6. The extra
quadratic column is used only for replacement; it is not a final generator. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg

theorem allEvenLabel_card_add {d : ℕ} (hd : 3 ≤ d) (q h m e extra : ℕ) :
    Fintype.card (Label q (allEvenIndices d) (allEvenCount d h m (e+extra)))=
      Fintype.card (Label q (allEvenIndices d) (allEvenCount d h m e))+extra := by
  rw [allEvenLabel_card hd,allEvenLabel_card hd,preparedLabel_card,preparedLabel_card,
    sum_targetLayerCount hd,sum_targetLayerCount hd]
  omega

theorem exact_odd_comparison_card {d k h lo m a f e : ℕ} {upper : Bool}
    (hd : 3 ≤ d) (hc : ExactCountConditions d k h lo m a f e upper) (extra : ℕ) :
    Fintype.card (PreparedTarget.Label (upperCount m d) f (tailGeneratorCount d h)
      (allEvenIndices d) (allEvenCount d h m (e+extra)))=
        adjacentCriticalCount upper (m+h) d+extra := by
  change Fintype.card (Label (upperCount m d) (allEvenIndices d)
    (allEvenCount d h m (e+extra)) ⊕ (Fin f ⊕ Fin (tailGeneratorCount d h)))=_
  rw [Fintype.card_sum]
  rw [show Fintype.card (Fin f ⊕ Fin (tailGeneratorCount d h))=f+tailGeneratorCount d h by simp]
  rw [allEvenLabel_card_add hd,allEvenLabel_card hd,preparedLabel_card,sum_targetLayerCount hd]
  have ht := hc.total
  unfold auxiliaryGeneratorCount at ht
  omega

theorem exact_even_comparison_card {d k h lo m a f e : ℕ} {upper : Bool}
    (hd : 3 ≤ d) (hc : ExactCountConditions d k h lo m a f e upper) (extra : ℕ) :
    Fintype.card (Label (upperCount m d) (allEvenIndices d)
      (allEvenCount d h m (e+tailGeneratorCount d h+extra)) ⊕ Fin f)=
        adjacentCriticalCount upper (m+h) d+extra := by
  rw [Fintype.card_sum,Fintype.card_fin,
    show e+tailGeneratorCount d h+extra=e+(tailGeneratorCount d h+extra) by omega,
    allEvenLabel_card_add hd,allEvenLabel_card hd,preparedLabel_card,sum_targetLayerCount hd]
  have ht := hc.total
  unfold auxiliaryGeneratorCount at ht
  omega

/-- This is the final restored-even enumeration; `extra=1` is the temporary
background with the one additional mixed quadratic generator. -/
def evenComparisonLabelEquiv {d k h lo m a f e : ℕ} {upper : Bool}
    (hd : 3 ≤ d) (hc : ExactCountConditions d k h lo m a f e upper) (extra : ℕ) :
    Fin (adjacentCriticalCount upper (m+h) d+extra) ≃
      (Label (upperCount m d) (allEvenIndices d)
        (allEvenCount d h m (e+tailGeneratorCount d h+extra)) ⊕ Fin f) :=
  ((Fintype.equivFin _).trans (finCongr (exact_even_comparison_card hd hc extra))).symm

def oddComparisonLabelEquiv {d k h lo m a f e : ℕ} {upper : Bool}
    (hd : 3 ≤ d) (hc : ExactCountConditions d k h lo m a f e upper) (extra : ℕ) :
    Fin (adjacentCriticalCount upper (m+h) d+extra) ≃
      PreparedTarget.Label (upperCount m d) f (tailGeneratorCount d h)
        (allEvenIndices d) (allEvenCount d h m (e+extra)) :=
  ((Fintype.equivFin _).trans (finCongr (exact_odd_comparison_card hd hc extra))).symm

end Froberg.PreparedParameters

namespace Froberg
open Filter
variable {K : Type} [Field K] [Infinite K] {d h : ℕ}

theorem eventual_recurrence_of_core_first_comparison
    (hD : ∀ᶠ m in atTop,∀ upper : Bool,Nonempty (LocalComparisonData K (h+m) d
      (adjacentCriticalCount upper (h+m) d) (criticalDefect K m d))) :
    ∃ start : ℕ,∀ m,start ≤ m → criticalDefect K (m+h) d ≤ criticalDefect K m d := by
  apply eventual_recurrence_of_comparison_data
  simpa only [Nat.add_comm h] using hD

end Froberg
