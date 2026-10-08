import Quartic.FiniteEndpointMetadata19Checks
open Quartic.FiniteEndpointMetadata19Data Quartic.FiniteEndpointCheckerPolynomial
set_option maxHeartbeats 2000000
namespace Quartic.FiniteEndpointMetadata19

theorem vars2_decoder (i : Fin 190) : tupleRank 19 0 (vars2 i)=i.val := (quad_checked i).1
theorem vars2_sorted (i : Fin 190) : (vars2 i).Pairwise (· ≤ ·) := (quad_checked i).2
theorem exponent2_injective : Function.Injective exponent2 :=
  listExponent_injective_of_sorted vars2 (injective_of_tupleRank vars2 vars2_decoder) vars2_sorted

theorem quartic_checked (i : Fin 7315) : tupleRank 19 0 (vars4 i)=i.val ∧
    (vars4 i).Pairwise (· ≤ ·) ∧ selectedGenerator i.val < 44 ∧
    selectedMultiplier i.val < 190 ∧ (i.val < 7267 → selectedGenerator i.val < 43) := by
  have h := quartic_all i.val i.isLt
  have hi : (⟨i.val%7315,Nat.mod_lt _ (by decide)⟩ : Fin 7315)=i :=
    Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simpa only [quarticCondition,hi] using h

theorem vars4_decoder (i : Fin 7315) : tupleRank 19 0 (vars4 i)=i.val := (quartic_checked i).1
theorem vars4_sorted (i : Fin 7315) : (vars4 i).Pairwise (· ≤ ·) := (quartic_checked i).2.1
theorem exponent4_injective : Function.Injective exponent4 :=
  listExponent_injective_of_sorted vars4 (injective_of_tupleRank vars4 vars4_decoder) vars4_sorted

theorem product_checked (i j : Fin 190) : naturalProduct i.val j.val < 7315 ∧
    vars4 (productIndex i j) = (vars2 i ++ vars2 j).insertionSort (· ≤ ·) := by
  have h := product_all (i.val*190+j.val) (by omega)
  have hi : (i.val*190+j.val)/190%190=i.val := by omega
  have hj : (i.val*190+j.val)%190=j.val := by omega
  simpa only [productCondition,hi,hj] using h

theorem product_bound (i j : Fin 190) : naturalProduct i.val j.val < 7315 := (product_checked i j).1

theorem product_exponents (i j : Fin 190) : exponent4 (productIndex i j)=exponent2 i+exponent2 j := by
  unfold exponent4 exponent2
  rw [(product_checked i j).2,listExponent_sort,listExponent_append]

theorem product_supports (i : Fin 7315) : (rows i).map exponent4 =
    (quadSupport (selected i).1).map (fun j => exponent2 j+exponent2 (selected i).2) :=
  FiniteEndpointProductRows.product_supports exponent2 exponent4 productIndex
    product_exponents quadSupport selected i

theorem naturalRow_bound (i : ℕ) : ∀ j ∈ naturalRow i,j < 7315 := by
  intro j hj
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hj
  exact product_bound k (selectedRaw i).2

theorem lower_selected (i : Fin 7267) : (selected ⟨i.val,by omega⟩).1.val < 43 := by
  have h := (quartic_checked ⟨i.val,by omega⟩).2.2.2.2 i.isLt
  change selectedGenerator i.val < 43 at h
  change selectedGenerator i.val % 44 < 43
  rw [Nat.mod_eq_of_lt (by omega)]
  exact h

#print axioms exponent2_injective
#print axioms exponent4_injective
#print axioms product_exponents
#print axioms product_supports
#print axioms naturalRow_bound
#print axioms lower_selected
end Quartic.FiniteEndpointMetadata19
