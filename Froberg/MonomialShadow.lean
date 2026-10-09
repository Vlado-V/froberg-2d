module

public import Froberg.MonomialIncidence

@[expose] public section

/-! Quantitative expansion of the shadow of any homogeneous monomial set. -/
noncomputable section
namespace Froberg.MonomialExpansion
open Finset

/-- The triples whose first factor belongs to the set and whose second does not. -/
abbrev MixedTriple {n e : ℕ} (d : ℕ) (A : Finset (Degree n e)) :=
  (↑A × {b : Degree n e // b ∉ A}) × Degree n (d - e)

/-- Multiplying the three factors gives a mixed target. -/
def tripleTarget {n e d : ℕ} (hed : e ≤ d) (A : Finset (Degree n e))
    (x : MixedTriple d A) : Degree n (e + d) :=
  ⟨x.1.1.val.val + x.1.2.val.val + x.2.val,
    mem_exponents.mpr (by simp only [map_add, degree_val]; omega)⟩

theorem tripleTarget_mem_mixed {n e d : ℕ} (hed : e ≤ d) (A : Finset (Degree n e))
    (x : MixedTriple d A) : tripleTarget hed A x ∈ mixed d A := by
  apply mem_filter.mpr
  constructor
  · apply mem_filter.mpr
    refine ⟨mem_univ _, x.1.1.val, x.1.1.property, ?_⟩
    change x.1.1.val.val ≤ x.1.1.val.val + x.1.2.val.val + x.2.val
    exact (le_self_add).trans le_self_add
  · refine ⟨x.1.2.val, x.1.2.property, ?_⟩
    change x.1.2.val.val ≤ x.1.1.val.val + x.1.2.val.val + x.2.val
    exact le_add_self.trans le_self_add

/-- Recording the target and the first two factors is injective. -/
def tripleEmbedding {n e d : ℕ} (hed : e ≤ d) (A : Finset (Degree n e)) :
    MixedTriple d A ↪ Σ b : ↑(mixed d A), DivisorPair b.val.val e where
  toFun x :=
    ⟨⟨tripleTarget hed A x, tripleTarget_mem_mixed hed A x⟩,
      ⟨⟨x.1.1.val.val, mem_filter.mpr ⟨x.1.1.val.property,
        le_self_add.trans le_self_add⟩⟩,
       ⟨x.1.2.val.val, mem_filter.mpr ⟨x.1.2.val.property, by
         change x.1.2.val.val ≤
           (x.1.1.val.val + x.1.2.val.val + x.2.val) - x.1.1.val.val
         simpa only [add_assoc, add_tsub_cancel_left] using
           (le_self_add : x.1.2.val.val ≤ x.1.2.val.val + x.2.val)⟩⟩⟩⟩
  inj' := by
    intro x y h
    have ha := congrArg (fun z : Σ b : ↑(mixed d A), DivisorPair b.val.val e => z.2.1.val) h
    have hb := congrArg (fun z : Σ b : ↑(mixed d A), DivisorPair b.val.val e => z.2.2.val) h
    have ht := congrArg (fun z : Σ b : ↑(mixed d A), DivisorPair b.val.val e => z.1.val.val) h
    change x.1.1.val.val = y.1.1.val.val at ha
    change x.1.2.val.val = y.1.2.val.val at hb
    change x.1.1.val.val + x.1.2.val.val + x.2.val =
      y.1.1.val.val + y.1.2.val.val + y.2.val at ht
    rw [ha, hb] at ht
    have hc := add_left_cancel ht
    exact Prod.ext (Prod.ext (Subtype.ext (Subtype.ext ha))
      (Subtype.ext (Subtype.ext hb))) (Subtype.ext hc)

/-- Each mixed monomial receives at most the product of the two divisor counts. -/
theorem triple_count_le_mixed {n e d : ℕ} (hed : e ≤ d) (A : Finset (Degree n e)) :
    A.card * ((n + e - 1).choose e - A.card) * (n + (d - e) - 1).choose (d - e) ≤
      (e + d).choose e * d.choose e * (mixed d A).card := by
  have hinj := Fintype.card_le_of_embedding (tripleEmbedding hed A)
  have htarget : Fintype.card (Σ b : ↑(mixed d A), DivisorPair b.val.val e) ≤
      (mixed d A).card * ((e + d).choose e * d.choose e) := by
    rw [Fintype.card_sigma]
    calc
      (∑ b : ↑(mixed d A), Fintype.card (DivisorPair b.val.val e)) ≤
          ∑ _b : ↑(mixed d A), (e + d).choose e * d.choose e := by
        apply sum_le_sum
        intro b _
        simpa only [degree_val, Nat.add_sub_cancel_left] using
          card_divisorPair_le b.val.val e
      _ = _ := by simp
  have hsource : Fintype.card (MixedTriple d A) =
      A.card * ((n + e - 1).choose e - A.card) * (n + (d - e) - 1).choose (d - e) := by
    simp only [MixedTriple, Fintype.card_prod, Fintype.card_coe,
      Fintype.card_subtype_compl, card_exponents]
  rw [hsource] at hinj
  exact (hinj.trans htarget).trans_eq (Nat.mul_comm _ _)

end Froberg.MonomialExpansion
