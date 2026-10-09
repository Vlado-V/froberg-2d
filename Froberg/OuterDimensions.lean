module

public import Froberg.OuterInjection

@[expose] public section

/-! Exact source and target dimensions in the actual outer presentation. -/
noncomputable section
namespace Froberg.OuterInjection
open Module

@[simp] theorem card_labels (k a s : ℕ) :
    Fintype.card (Labels k a s) = k * (a+s-1).choose s := by
  simp [Labels, Sym.card_sym_eq_choose]

/-- The same concrete attached-vector family has the exact source and target
quotient dimensions asserted in B.2, for arbitrary attachment multiplicity. -/
theorem exists_outer_presentation {K : Type*} [Field K] [Infinite K]
    (k a z s h : ℕ) (hn : 0 < a+z)
    (hh : k * (2*s+1).choose s ≤ h) :
    ∃ v : Labels k a s → Fin h → K,
      (∀ c ≤ s+1, Function.Injective
        (AttachedMultiplication.multiplication (d := c) (coreExponent z) v)) ∧
      finrank K ((Fin h → Forms K (a+z) s) ⧸
        AttachedMultiplication.relationSpace (d := 0) (coreExponent z) v (coreExponent_degree z)) =
          h * (a+z+s-1).choose s - k * (a+s-1).choose s ∧
      finrank K ((Fin h → Forms K (a+z) (s+(s+1))) ⧸
        AttachedMultiplication.relationSpace (d := s+1) (coreExponent z) v (coreExponent_degree z)) =
          h * (a+z+(2*s+1)-1).choose (2*s+1) -
            k * (a+s-1).choose s * (a+z+(s+1)-1).choose (s+1) := by
  have hs : s+(s+1) = 2*s+1 := by omega
  obtain ⟨v,hv⟩ := exists_injective_attached_multiplication_through (K := K)
    k a z s (s+1) h (by simpa only [hs] using hh)
  refine ⟨v,hv,?_,?_⟩
  · have hd := AttachedMultiplication.quotient_finrank_of_injective
      (coreExponent z) v (coreExponent_degree z) hn (hv 0 (by omega))
    simpa only [Fintype.card_fin, card_labels, Nat.add_zero, Nat.choose_zero_right, mul_one] using hd
  · have hd := AttachedMultiplication.quotient_finrank_of_injective
      (coreExponent z) v (coreExponent_degree z) hn (hv (s+1) le_rfl)
    simpa only [Fintype.card_fin, card_labels, hs] using hd

end Froberg.OuterInjection
