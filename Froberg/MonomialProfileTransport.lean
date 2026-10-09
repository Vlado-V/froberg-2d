module

public import Froberg.ProfileTransport
public import Froberg.DivisibilityCoupling
public import Froberg.FiberTransport
public import Froberg.BidegreeExponents

@[expose] public section

/-! The explicit profile transport lifted to the actual two-block monomials.
No squarefreeness hypothesis is used. -/
noncomputable section
namespace Froberg
open Finset MonomialExpansion

def SourceMonomialFiber (a z s : ℕ) (i : Option (Fin s)) :=
  Degree a (profileSourceIndex i) × Degree z (s - profileSourceIndex i)

def TargetMonomialFiber (a z s : ℕ) (j : Fin (2 * s + 1)) :=
  Degree a j × Degree z (2 * s + 1 - j)

instance (a z s : ℕ) (i : Option (Fin s)) : Fintype (SourceMonomialFiber a z s i) :=
  inferInstanceAs (Fintype (_ × _))
instance (a z s : ℕ) (j : Fin (2 * s + 1)) : Fintype (TargetMonomialFiber a z s j) :=
  inferInstanceAs (Fintype (_ × _))

lemma profileSourceIndex_le {s : ℕ} (i : Option (Fin s)) : profileSourceIndex i ≤ s := by
  cases i <;> simp only [profileSourceIndex] <;> omega

def localMonomialCoupling {a z s : ℕ} (i : Option (Fin s)) (j : Fin (2 * s + 1)) :
    SourceMonomialFiber a z s i → TargetMonomialFiber a z s j → ℝ :=
  productTransport divisibilityCoupling divisibilityCoupling

lemma localMonomialCoupling_row {a z s : ℕ} (ha : 0 < a) (hz : 0 < z)
    (i : Option (Fin s)) (j : Fin (2 * s + 1)) (hij : profileAllowed i j)
    (α : SourceMonomialFiber a z s i) :
    ∑ β, localMonomialCoupling i j α β = 1 / (Fintype.card (SourceMonomialFiber a z s i) : ℝ) := by
  have hfree : s - profileSourceIndex i ≤ 2 * s + 1 - j := by
    have hi := profileSourceIndex_le i
    rcases hij with ⟨h₁, h₂⟩
    omega
  apply productTransport_row
  · intro α
    simpa only [card_degree] using divisibilityCoupling_row ha hij.1 α
  · intro α
    simpa only [card_degree] using divisibilityCoupling_row hz hfree α

lemma localMonomialCoupling_column {a z s : ℕ} (ha : 0 < a) (hz : 0 < z)
    (i : Option (Fin s)) (j : Fin (2 * s + 1)) (hij : profileAllowed i j)
    (β : TargetMonomialFiber a z s j) :
    ∑ α, localMonomialCoupling i j α β = 1 / (Fintype.card (TargetMonomialFiber a z s j) : ℝ) := by
  have hfree : s - profileSourceIndex i ≤ 2 * s + 1 - j := by
    have hi := profileSourceIndex_le i
    rcases hij with ⟨h₁, h₂⟩
    omega
  apply productTransport_column
  · intro β
    simpa only [card_degree] using divisibilityCoupling_column ha hij.1 β
  · intro β
    simpa only [card_degree] using divisibilityCoupling_column hz hfree β

lemma localMonomialCoupling_nonneg {a z s : ℕ}
    (i : Option (Fin s)) (j : Fin (2 * s + 1))
    (α : SourceMonomialFiber a z s i) (β : TargetMonomialFiber a z s j) :
    0 ≤ localMonomialCoupling i j α β :=
  mul_nonneg (divisibilityCoupling_nonneg α.1 β.1) (divisibilityCoupling_nonneg α.2 β.2)

lemma localMonomialCoupling_pos_iff {a z s : ℕ} (ha : 0 < a) (hz : 0 < z)
    (i : Option (Fin s)) (j : Fin (2 * s + 1)) (hij : profileAllowed i j)
    (α : SourceMonomialFiber a z s i) (β : TargetMonomialFiber a z s j) :
    0 < localMonomialCoupling i j α β ↔
      OuterInjection.joinParts α.1.val α.2.val ≤ OuterInjection.joinParts β.1.val β.2.val := by
  have hfree : s - profileSourceIndex i ≤ 2 * s + 1 - j := by
    have hi := profileSourceIndex_le i
    rcases hij with ⟨h₁, h₂⟩
    omega
  change 0 < divisibilityCoupling α.1 β.1 * divisibilityCoupling α.2 β.2 ↔ _
  rw [OuterInjection.joinParts_le_joinParts, ← divisibilityCoupling_pos_iff ha hij.1,
    ← divisibilityCoupling_pos_iff hz hfree, mul_pos_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact False.elim ((not_lt_of_ge (divisibilityCoupling_nonneg α.1 β.1)) h.1)
  · exact Or.inl

/-- Joint distribution on individual source and target monomials. -/
def monomialProfileJoint {a z s : ℕ}
    (P : Option (Fin s) → Fin (2 * s + 1) → ℝ) :
    (Σ i, SourceMonomialFiber a z s i) → (Σ j, TargetMonomialFiber a z s j) → ℝ :=
  fiberTransport P localMonomialCoupling

lemma monomialProfileJoint_row {a z s : ℕ} (ha : 0 < a) (hz : 0 < z)
    (P : Option (Fin s) → Fin (2 * s + 1) → ℝ) (p : Option (Fin s) → ℝ)
    (hP : ∀ i, ∑ j, P i j = p i) (hPzero : ∀ i j, ¬profileAllowed i j → P i j = 0)
    (α : Σ i, SourceMonomialFiber a z s i) :
    ∑ β, monomialProfileJoint P α β = p α.1 / (Fintype.card (SourceMonomialFiber a z s α.1) : ℝ) := by
  apply fiberTransport_row P localMonomialCoupling p hP
  intro i j hij α
  exact localMonomialCoupling_row ha hz i j (by by_contra h; exact hij (hPzero i j h)) α

lemma monomialProfileJoint_column {a z s : ℕ} (ha : 0 < a) (hz : 0 < z)
    (P : Option (Fin s) → Fin (2 * s + 1) → ℝ) (q : Fin (2 * s + 1) → ℝ)
    (hP : ∀ j, ∑ i, P i j = q j) (hPzero : ∀ i j, ¬profileAllowed i j → P i j = 0)
    (β : Σ j, TargetMonomialFiber a z s j) :
    ∑ α, monomialProfileJoint P α β = q β.1 / (Fintype.card (TargetMonomialFiber a z s β.1) : ℝ) := by
  apply fiberTransport_column P localMonomialCoupling q hP
  intro i j hij β
  exact localMonomialCoupling_column ha hz i j (by by_contra h; exact hij (hPzero i j h)) β

lemma monomialProfileJoint_nonneg {a z s : ℕ}
    (P : Option (Fin s) → Fin (2 * s + 1) → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (α : Σ i, SourceMonomialFiber a z s i) (β : Σ j, TargetMonomialFiber a z s j) :
    0 ≤ monomialProfileJoint P α β :=
  fiberTransport_nonneg P localMonomialCoupling hP localMonomialCoupling_nonneg α β

end Froberg
