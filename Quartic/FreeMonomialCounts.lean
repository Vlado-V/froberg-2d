import Quartic.FreePieces
import Quartic.ProfileCertificate.Core

/-!
# Counts of free monomials meeting a chosen set of variables

Repeated variables are retained: monomials are symmetric powers, equivalently
nonnegative exponent vectors of the given total degree. These are the actual
index sets used by the free-coefficient decomposition.
-/

noncomputable section
namespace Quartic.FreeMonomialCounts
open Quartic.FreeCoefficients

/-- Symmetric powers of a subset are precisely the monomials supported there. -/
def symSubtypeEquiv {α : Type*} (P : α → Prop) (k : ℕ) :
    Sym {a // P a} k ≃ {s : Sym α k // ∀ a ∈ s, P a} where
  toFun s := ⟨s.map Subtype.val, by
    intro a ha
    obtain ⟨b, _, rfl⟩ := Sym.mem_map.mp ha
    exact b.property⟩
  invFun s := s.val.attach.map (fun a => ⟨a.val, s.property a.val a.property⟩)
  left_inv s := by
    apply Sym.map_injective Subtype.val_injective k
    rw [Sym.map_map]
    exact Sym.attach_map_coe (s.map Subtype.val)
  right_inv s := by
    apply Subtype.ext
    change Sym.map Subtype.val (Sym.map _ s.val.attach) = s.val
    rw [Sym.map_map]
    exact Sym.attach_map_coe s.val

/-- Number of degree-`k` monomials supported on a selected finite set. -/
theorem supported_card {α : Type*} [Fintype α] [DecidableEq α]
    (P : α → Prop) [DecidablePred P] (k : ℕ) :
    Fintype.card {s : Sym α k // ∀ a ∈ s, P a} =
      (Fintype.card {a // P a} + k - 1).choose k := by
  rw [← Fintype.card_congr (symSubtypeEquiv P k), Sym.card_sym_eq_choose]

/-- Number of free monomials containing at least one variable in a chosen subset. -/
theorem meeting_card {α : Type*} [Fintype α] [DecidableEq α]
    (P : α → Prop) [DecidablePred P] (k : ℕ) :
    Fintype.card {s : Sym α k // ∃ a ∈ s, P a} =
      (Fintype.card α + k - 1).choose k -
        (Fintype.card α - Fintype.card {a // P a} + k - 1).choose k := by
  classical
  have hc : Fintype.card {s : Sym α k // ∃ a ∈ s, P a} =
      Fintype.card {s : Sym α k // ¬ (∀ a ∈ s, ¬ P a)} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun s => by simp))
  rw [hc, Fintype.card_subtype_compl, supported_card, Sym.card_sym_eq_choose,
    Fintype.card_subtype_compl]

/-- Degree-exact exponent vectors inherit the finite monomial index set. -/
abbrev ExactExponent (w k : ℕ) := {b : Fin w →₀ ℕ // b.degree = k}

instance exactExponentFinite (w k : ℕ) : Finite (ExactExponent w k) :=
  Finite.of_equiv (Sym (Fin w) k) (Quartic.exponentEquiv w k)

noncomputable instance exactExponentFintype (w k : ℕ) : Fintype (ExactExponent w k) :=
  Fintype.ofFinite _

theorem exactExponent_card (w k : ℕ) :
    Fintype.card (ExactExponent w k) = (w + k - 1).choose k := by
  rw [← Fintype.card_congr (Quartic.exponentEquiv w k), Sym.card_sym_eq_choose]
  simp

/-- Membership of the monomial multiset agrees with positivity of its exponent. -/
theorem exponent_pos_iff (s : Sym (Fin w) k) (i : Fin w) :
    0 < (Quartic.exponentEquiv w k s).val i ↔ i ∈ s := by
  change 0 < (s : Multiset (Fin w)).count i ↔ _
  exact Multiset.count_pos

/-- The binomial count holds for the actual exponent vectors in free coefficients. -/
theorem exponent_meeting_card (w k : ℕ) (P : Fin w → Prop) [DecidablePred P] :
    Fintype.card {b : ExactExponent w k // ∃ i, P i ∧ 0 < b.val i} =
      (w + k - 1).choose k - (w - Fintype.card {i // P i} + k - 1).choose k := by
  classical
  let e : {s : Sym (Fin w) k // ∃ i ∈ s, P i} ≃
      {b : ExactExponent w k // ∃ i, P i ∧ 0 < b.val i} :=
    (Quartic.exponentEquiv w k).subtypeEquiv (by
      intro s
      simp only [exponent_pos_iff]
      exact exists_congr fun i => and_comm)
  rw [← Fintype.card_congr e]
  have h := meeting_card P k
  simp only [← Nat.card_eq_fintype_card, Nat.card_fin] at h ⊢
  exact h

/-- The manuscript's quadratic shadow count counts exactly the incident free monomials. -/
theorem h2_counts_monomials (w : ℕ) (P : Fin w → Prop) [DecidablePred P] :
    (Fintype.card {b : ExactExponent w 2 // ∃ i, P i ∧ 0 < b.val i} : ℤ) =
      ProfileCertificate.h2 w (Fintype.card {i // P i}) := by
  rw [exponent_meeting_card, ProfileCertificate.h2_eq_binomial]
  have hcalc (v : ℕ) : v + 2 - 1 = v + 1 := by omega
  simp only [hcalc]
  rw [Int.natCast_sub (Nat.choose_le_choose 2 (by omega))]

/-- The cubic count includes repeated free variables in the same way. -/
theorem h3_counts_monomials (w : ℕ) (P : Fin w → Prop) [DecidablePred P] :
    (Fintype.card {b : ExactExponent w 3 // ∃ i, P i ∧ 0 < b.val i} : ℤ) =
      ProfileCertificate.h3 w (Fintype.card {i // P i}) := by
  rw [exponent_meeting_card, ProfileCertificate.h3_eq_binomial]
  have hcalc (v : ℕ) : v + 3 - 1 = v + 2 := by omega
  simp only [hcalc]
  rw [Int.natCast_sub (Nat.choose_le_choose 3 (by omega))]

end Quartic.FreeMonomialCounts
