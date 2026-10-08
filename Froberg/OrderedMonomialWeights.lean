import Froberg.OrderedMonomials
import Froberg.MonomialExpansionBound

/-! Exact biregular incidence weights in increasing monomial coordinates. -/
noncomputable section
namespace Froberg
open Finset MonomialExpansion Quartic.HomogeneousCoefficientCoordinates

private def exponentToDegree (n e : ℕ) : Exponent n e ≃ Degree n e where
  toFun a := ⟨a.val,mem_exponents.mpr a.property⟩
  invFun a := ⟨a.val,degree_val a⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def orderedToDegree (n e : ℕ) :
    Fin (Fintype.card (Exponent n e)) ≃ Degree n e :=
  (OrderedMonomials.enumerate n e).trans (exponentToDegree n e)

theorem card_coefficient_exponent (n e : ℕ) :
    Fintype.card (Exponent n e) = (n+e-1).choose e := by
  rw [Fintype.card_congr (exponentToDegree n e),card_degree]

def orderedMonomialWeight {n e d : ℕ}
    (k : Fin (Fintype.card (Exponent n (e+d))))
    (j : Fin (Fintype.card (Exponent n e))) : ℕ :=
  weight (OrderedMonomials.enumerate n (e+d) k).val
    (OrderedMonomials.enumerate n e j).val

theorem orderedMonomialWeight_row {n e d : ℕ}
    (k : Fin (Fintype.card (Exponent n (e+d)))) :
    ∑ j, orderedMonomialWeight (d := d) k j = (e+d).choose e := by
  have hh := (orderedToDegree n e).sum_comp
    (fun a => weight (OrderedMonomials.enumerate n (e+d) k).val a.val)
  change (∑ j, orderedMonomialWeight k j) = _ at hh
  rw [hh]
  exact weighted_row (orderedToDegree n (e+d) k)

theorem orderedMonomialWeight_column {n e d : ℕ} (hn : 0 < n)
    (j : Fin (Fintype.card (Exponent n e))) :
    ∑ k, orderedMonomialWeight (d := d) k j = (n+e+d-1).choose d := by
  have hh := (orderedToDegree n (e+d)).sum_comp
    (fun b => weight b.val (OrderedMonomials.enumerate n e j).val)
  change (∑ k, orderedMonomialWeight k j) = _ at hh
  rw [hh]
  exact weighted_column hn (orderedToDegree n e j)

theorem orderedMonomialWeight_support {n e d : ℕ}
    (k : Fin (Fintype.card (Exponent n (e+d))))
    (j : Fin (Fintype.card (Exponent n e)))
    (h : 0 < orderedMonomialWeight k j) :
    ∃ b : Exponent n d, OrderedMonomials.shift b j = k := by
  have hab := (weight_pos_iff _ _).mp h
  obtain ⟨c,hc⟩ := exists_add_of_le hab
  have hcdeg : c.degree=d := by
    have hg := congrArg Finsupp.degree hc
    simp only [map_add] at hg
    have hs := (OrderedMonomials.enumerate n e j).property
    have ht := (OrderedMonomials.enumerate n (e+d) k).property
    omega
  refine ⟨⟨c,hcdeg⟩,?_⟩
  apply (OrderedMonomials.enumerate n (e+d)).injective
  rw [OrderedMonomials.enumerate_shift]
  apply Subtype.ext
  exact hc.symm

end Froberg
