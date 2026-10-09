module

public import Froberg.FiberDimensions
public import Froberg.RepeatedMonomials

@[expose] public section

/-! Exact core-divisor counts and the repeated-variable error in coarse
outer-module capacities. -/
noncomputable section
namespace Froberg.OuterInjection
open Finset Module

lemma coreExponent_le_iff {k a z s : ℕ} (i : Labels k a s) (β : Fin (a + z) →₀ ℕ) :
    coreExponent z i ≤ β ↔ (exponentEquiv a s i.2).val ≤ corePart β := by
  constructor
  · exact core_divisor_le β i
  · intro h j
    by_cases hj : j ∈ Set.range (Fin.castAdd z : Fin a → Fin (a + z))
    · obtain ⟨l, rfl⟩ := hj
      simpa only [coreExponent, Finsupp.mapDomain_apply_of_injective (Fin.castAdd_injective a z),
        corePart_apply] using h l
    · rw [coreExponent, Finsupp.mapDomain_of_notMem_range _ _ hj]
      exact Nat.zero_le _

/-- Labels dividing a target are exactly a copy of each core divisor
for each of the k attached vectors. -/
def targetLabelsEquiv (k a z s : ℕ) (β : Fin (a + z) →₀ ℕ) :
    {i : Labels k a s // coreExponent z i ≤ β} ≃
      Fin k × MonomialExpansion.Divisor (corePart β) s where
  toFun i := (i.val.1, ⟨(exponentEquiv a s i.val.2).val,
    mem_filter.mpr ⟨MonomialExpansion.mem_exponents.mpr (exponentEquiv a s i.val.2).property,
      (coreExponent_le_iff i.val β).mp i.property⟩⟩)
  invFun p := ⟨(p.1, (exponentEquiv a s).symm
    ⟨p.2.val, MonomialExpansion.divisor_degree p.2⟩), by
      apply (coreExponent_le_iff _ β).mpr
      simpa only [Equiv.apply_symm_apply] using MonomialExpansion.divisor_le p.2⟩
  left_inv i := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (exponentEquiv a s).symm_apply_apply i.val.2
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change ((exponentEquiv a s) ((exponentEquiv a s).symm
        ⟨p.2.val, MonomialExpansion.divisor_degree p.2⟩)).val = p.2.val
      rw [Equiv.apply_symm_apply]

lemma card_target_labels_exact {k a z s : ℕ} (β : Fin (a + z) →₀ ℕ) :
    Fintype.card {i : Labels k a s // coreExponent z i ≤ β} =
      k * Fintype.card (MonomialExpansion.Divisor (corePart β) s) := by
  rw [Fintype.card_congr (targetLabelsEquiv k a z s β), Fintype.card_prod, Fintype.card_fin]

lemma card_target_labels_squarefree {k a z s : ℕ} (β : Fin (a + z) →₀ ℕ)
    (hβ : ∀ i, corePart β i ≤ 1) :
    Fintype.card {i : Labels k a s // coreExponent z i ≤ β} =
      k * (corePart β).degree.choose s := by
  rw [card_target_labels_exact, MonomialExpansion.card_divisors_squarefree _ _ hβ]

end Froberg.OuterInjection

namespace Froberg.AttachedMultiplication
open Module Finset
variable {K : Type*} [Field K]

lemma core_quotientFiber_squarefree {k a z s h : ℕ}
    (v : OuterInjection.Labels k a s → Fin h → K) (β : Fin (a + z) →₀ ℕ)
    (hi : LinearIndependent K
      (fun i : {i : OuterInjection.Labels k a s // OuterInjection.coreExponent z i ≤ β} => v i.val))
    (hβ : ∀ i, OuterInjection.corePart β i ≤ 1) :
    finrank K ((Fin h → K) ⧸ relationFiber (OuterInjection.coreExponent z) v β) =
      h - k * (OuterInjection.corePart β).degree.choose s := by
  rw [quotientFiber_finrank _ _ β hi, Fintype.card_fin,
    OuterInjection.card_target_labels_squarefree β hβ]

/-- The total exact target dimension differs from the coarse total only
on repeated-variable monomials, whose number is one order smaller. -/
theorem coarse_target_error {k a z s h r : ℕ}
    (v : OuterInjection.Labels k a s → Fin h → K)
    (hi : ∀ β : MonomialExpansion.Degree (a + z) r, LinearIndependent K
      (fun i : {i : OuterInjection.Labels k a s // OuterInjection.coreExponent z i ≤ β.val} => v i.val)) :
    (∑ β : MonomialExpansion.Degree (a + z) r,
      finrank K ((Fin h → K) ⧸ relationFiber (OuterInjection.coreExponent z) v β.val)) ≤
    (∑ β : MonomialExpansion.Degree (a + z) r,
      (h - k * (OuterInjection.corePart β.val).degree.choose s)) +
      h * (a + z) * (a + z + (r - 2) - 1).choose (r - 2) := by
  classical
  have hp (β : MonomialExpansion.Degree (a + z) r) :
      finrank K ((Fin h → K) ⧸ relationFiber (OuterInjection.coreExponent z) v β.val) ≤
        (h - k * (OuterInjection.corePart β.val).degree.choose s) +
          if ∃ i, 2 ≤ β.val i then h else 0 := by
    by_cases hb : ∃ i, 2 ≤ β.val i
    · rw [if_pos hb, quotientFiber_finrank _ _ β.val (hi β), Fintype.card_fin]
      omega
    · rw [if_neg hb, add_zero, core_quotientFiber_squarefree v β.val (hi β)]
      intro i
      have hh : ¬2 ≤ β.val (Fin.castAdd z i) := fun h => hb ⟨_, h⟩
      change β.val (Fin.castAdd z i) ≤ 1
      omega
  have hs := sum_le_sum (fun β (_ : β ∈ (univ : Finset (MonomialExpansion.Degree (a + z) r))) => hp β)
  rw [sum_add_distrib] at hs
  have hsum : (∑ β : MonomialExpansion.Degree (a + z) r, if ∃ i, 2 ≤ β.val i then h else 0) =
      Fintype.card {β : MonomialExpansion.Degree (a + z) r // ∃ i, 2 ≤ β.val i} * h := by
    rw [Fintype.card_subtype]
    simp only [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul]
  rw [hsum] at hs
  have hc := Nat.mul_le_mul_right h (MonomialExpansion.card_repeated_monomials (a + z) r)
  nlinarith

end Froberg.AttachedMultiplication
