import Froberg.OuterFiberAction
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Data.Fintype.Sort

/-! Increasing monomial enumeration for block-valued initial subspaces. -/
noncomputable section
namespace Froberg.OrderedMonomials
open Quartic.HomogeneousCoefficientCoordinates

abbrev monomialOrder (n : ℕ) : MonomialOrder (Fin n) := MonomialOrder.lex

abbrev OrderedExponent (n d : ℕ) :=
  {a : (monomialOrder n).syn // ((monomialOrder n).toSyn.symm a).degree = d}

def orderedEquiv (n d : ℕ) : OrderedExponent n d ≃ Exponent n d where
  toFun a := ⟨(monomialOrder n).toSyn.symm a.val,a.property⟩
  invFun a := ⟨(monomialOrder n).toSyn a.val,by simpa using a.property⟩
  left_inv a := by apply Subtype.ext; simp
  right_inv a := by apply Subtype.ext; simp

instance orderedExponentFintype (n d : ℕ) : Fintype (OrderedExponent n d) :=
  Fintype.ofEquiv (Exponent n d) (orderedEquiv n d).symm

def orderedEnumeration (n d : ℕ) :
    Fin (Fintype.card (Exponent n d)) ≃o OrderedExponent n d :=
  Fintype.orderIsoFinOfCardEq _ (Fintype.card_congr (orderedEquiv n d))

def enumerate (n d : ℕ) : Fin (Fintype.card (Exponent n d)) ≃ Exponent n d :=
  (orderedEnumeration n d).toEquiv.trans (orderedEquiv n d)

@[simp] theorem toSyn_enumerate (n d : ℕ) (i : Fin (Fintype.card (Exponent n d))) :
    (monomialOrder n).toSyn (enumerate n d i).val = (orderedEnumeration n d i).val := by
  simp [enumerate,orderedEquiv]

theorem enumerate_lt_iff {n d : ℕ} (i j : Fin (Fintype.card (Exponent n d))) :
    (monomialOrder n).toSyn (enumerate n d i).val <
      (monomialOrder n).toSyn (enumerate n d j).val ↔ i < j := by
  rw [toSyn_enumerate,toSyn_enumerate]
  exact (orderedEnumeration n d).lt_iff_lt

def shift {n s d : ℕ} (b : Exponent n d) :
    Fin (Fintype.card (Exponent n s)) → Fin (Fintype.card (Exponent n (s+d))) :=
  fun i => (enumerate n (s+d)).symm (AttachedMultiplication.addExponent (enumerate n s i) b)

@[simp] theorem enumerate_shift {n s d : ℕ} (b : Exponent n d)
    (i : Fin (Fintype.card (Exponent n s))) :
    enumerate n (s+d) (shift b i) = AttachedMultiplication.addExponent (enumerate n s i) b := by
  simp [shift]

theorem shift_strictMono {n s d : ℕ} (b : Exponent n d) :
    StrictMono (shift (s := s) b) := by
  intro i j hij
  apply (enumerate_lt_iff (shift b i) (shift b j)).mp
  have hh := add_lt_add_right ((enumerate_lt_iff i j).mpr hij) ((monomialOrder n).toSyn b.val)
  simpa only [enumerate_shift,AttachedMultiplication.addExponent,map_add,add_comm] using hh

end Froberg.OrderedMonomials
