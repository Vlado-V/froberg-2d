import Froberg.OuterGeneric
import Froberg.OuterDimensions
import Froberg.AttachedProjection

/-! One concrete outer model with exact dimensions and uniform projection control. -/
noncomputable section
namespace Froberg.OuterInjection
open Module

/-- The label bound in the finite-set form used by the quotient projection theorem. -/
theorem core_labelsBelow_card_le {k a z s : ℕ} (b : Fin (a+z) →₀ ℕ) :
    (AttachedMultiplication.labelsBelow (coreExponent (k := k) (s := s) z) b).card ≤
      k * b.degree.choose s := by
  classical
  simpa only [AttachedMultiplication.labelsBelow,Fintype.card_subtype] using
    (card_target_labels_le (k := k) (s := s) z b)

/-- Exact dimensions for every injective attached presentation, so the same
presentation can be used in all subsequent generic and uniform assertions. -/
theorem outer_presentation_dimensions {K : Type*} [Field K]
    {k a z s h : ℕ} (hn : 0 < a+z) (v : Labels k a s → Fin h → K)
    (hi : ∀ c ≤ s+1, Function.Injective
      (AttachedMultiplication.multiplication (d := c) (coreExponent z) v)) :
    finrank K ((Fin h → Forms K (a+z) s) ⧸
      AttachedMultiplication.relationSpace (d := 0) (coreExponent z) v (coreExponent_degree z)) =
        h * (a+z+s-1).choose s - k * (a+s-1).choose s ∧
    finrank K ((Fin h → Forms K (a+z) (s+(s+1))) ⧸
      AttachedMultiplication.relationSpace (d := s+1) (coreExponent z) v (coreExponent_degree z)) =
        h * (a+z+(2*s+1)-1).choose (2*s+1) -
          k * (a+s-1).choose s * (a+z+(s+1)-1).choose (s+1) := by
  constructor
  · have hd := AttachedMultiplication.quotient_finrank_of_injective
      (coreExponent z) v (coreExponent_degree z) hn (hi 0 (by omega))
    simpa only [Fintype.card_fin,card_labels,Nat.add_zero,Nat.choose_zero_right,mul_one] using hd
  · have hd := AttachedMultiplication.quotient_finrank_of_injective
      (coreExponent z) v (coreExponent_degree z) hn (hi (s+1) le_rfl)
    simpa only [Fintype.card_fin,card_labels,show s+(s+1)=2*s+1 by omega] using hd

end Froberg.OuterInjection
