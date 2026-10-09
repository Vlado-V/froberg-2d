module

public import Quartic.FreePieces
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Data.Fintype.Sort

@[expose] public section

/-!
# Additively ordered finite free-monomial indices

Bounded free exponents are enumerated increasingly in the lexicographic
monomial order. Addition by any fixed bounded exponent induces a strictly
increasing map between the corresponding finite index types. The original
`BoundedExponent` carries no new order instance.
-/

noncomputable section
namespace Quartic.OrderedFreeExponents
open FreeCoefficients

/-- The lexicographic monomial order on the free variables. -/
abbrev monomialOrder (w : ℕ) : MonomialOrder (Fin w) := MonomialOrder.lex

/-- Bounded exponents represented inside the linearly ordered monomial synonym. -/
abbrev OrderedExponent (w d : ℕ) :=
  {b : (monomialOrder w).syn // ((monomialOrder w).toSyn.symm b).degree ≤ d}

/-- Passing to the monomial-order synonym changes no exponents or bounds. -/
def orderedEquiv (w d : ℕ) : OrderedExponent w d ≃ BoundedExponent w d where
  toFun b := ⟨(monomialOrder w).toSyn.symm b.val, b.property⟩
  invFun b := ⟨(monomialOrder w).toSyn b.val, by simpa using b.property⟩
  left_inv b := by apply Subtype.ext; simp
  right_inv b := by apply Subtype.ext; simp

instance orderedExponentFintype (w d : ℕ) : Fintype (OrderedExponent w d) :=
  Fintype.ofEquiv (BoundedExponent w d) (orderedEquiv w d).symm

/-- Increasing enumeration of the ordered synonym, with the original cardinality. -/
def orderedEnumeration (w d : ℕ) :
    Fin (Fintype.card (BoundedExponent w d)) ≃o OrderedExponent w d :=
  Fintype.orderIsoFinOfCardEq _ (Fintype.card_congr (orderedEquiv w d))

/-- A finite enumeration of the actual bounded exponents in monomial order. -/
def enumerate (w d : ℕ) :
    Fin (Fintype.card (BoundedExponent w d)) ≃ BoundedExponent w d :=
  (orderedEnumeration w d).toEquiv.trans (orderedEquiv w d)

@[simp] theorem toSyn_enumerate (w d : ℕ)
    (i : Fin (Fintype.card (BoundedExponent w d))) :
    (monomialOrder w).toSyn (enumerate w d i).val = (orderedEnumeration w d i).val := by
  simp [enumerate, orderedEquiv]

/-- The finite indices compare exactly as their lexicographic monomials do. -/
theorem enumerate_lt_iff {w d : ℕ}
    (i j : Fin (Fintype.card (BoundedExponent w d))) :
    (monomialOrder w).toSyn (enumerate w d i).val <
      (monomialOrder w).toSyn (enumerate w d j).val ↔ i < j := by
  rw [toSyn_enumerate, toSyn_enumerate]
  exact (orderedEnumeration w d).lt_iff_lt

/-- Addition of a multiplier exponent to an exponent in the source degree. -/
def addExponent {w d k : ℕ} (b : BoundedExponent w k) (c : BoundedExponent w d) :
    BoundedExponent w (d + k) :=
  ⟨b.val + c.val, by rw [map_add]; omega⟩

@[simp] theorem addExponent_val {w d k : ℕ}
    (b : BoundedExponent w k) (c : BoundedExponent w d) :
    (addExponent b c).val = b.val + c.val := rfl

/-- The finite target index obtained by adding the multiplier exponent. -/
def shift {w d k : ℕ} (b : BoundedExponent w k) :
    Fin (Fintype.card (BoundedExponent w d)) →
      Fin (Fintype.card (BoundedExponent w (d + k))) :=
  fun i => (enumerate w (d + k)).symm (addExponent b (enumerate w d i))

@[simp] theorem enumerate_shift {w d k : ℕ} (b : BoundedExponent w k)
    (i : Fin (Fintype.card (BoundedExponent w d))) :
    enumerate w (d + k) (shift b i) = addExponent b (enumerate w d i) := by
  simp [shift]

@[simp] theorem enumerate_shift_val {w d k : ℕ} (b : BoundedExponent w k)
    (i : Fin (Fintype.card (BoundedExponent w d))) :
    (enumerate w (d + k) (shift b i)).val = b.val + (enumerate w d i).val := by
  rw [enumerate_shift, addExponent_val]

/-- Translation by a fixed monomial strictly preserves the finite source order. -/
theorem shift_strictMono {w d k : ℕ} (b : BoundedExponent w k) :
    StrictMono (shift (d := d) b) := by
  intro i j hij
  apply (enumerate_lt_iff (w := w) (d := d + k) (shift b i) (shift b j)).mp
  have h := add_lt_add_left ((enumerate_lt_iff i j).mpr hij) ((monomialOrder w).toSyn b.val)
  simpa only [enumerate_shift_val, map_add, add_comm] using h

/-- In particular, fixed-exponent translation never identifies two source blocks. -/
theorem shift_injective {w d k : ℕ} (b : BoundedExponent w k) :
    Function.Injective (shift (d := d) b) := (shift_strictMono b).injective

/-- The shift needed for quadratic multiplication from degree one into degree three. -/
def quadraticShift {w : ℕ} (b : BoundedExponent w 2) :
    Fin (Fintype.card (BoundedExponent w 1)) → Fin (Fintype.card (BoundedExponent w 3)) :=
  shift b

theorem quadraticShift_strictMono {w : ℕ} (b : BoundedExponent w 2) :
    StrictMono (quadraticShift b) := shift_strictMono b

@[simp] theorem enumerate_quadraticShift_val {w : ℕ} (b : BoundedExponent w 2)
    (i : Fin (Fintype.card (BoundedExponent w 1))) :
    (enumerate w 3 (quadraticShift b i)).val = b.val + (enumerate w 1 i).val :=
  enumerate_shift_val b i

end Quartic.OrderedFreeExponents
