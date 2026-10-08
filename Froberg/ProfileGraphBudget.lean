import Quartic.IteratedBlockCharts

/-! A simple uniform budget for the literal iterated graph charts used in
C.4. Each kernel direction costs at most the whole source dimension. -/
noncomputable section
namespace Froberg
open Module Quartic.IteratedBlockCharts Quartic.SubspaceCharts
variable {n : ℕ} {b r : Fin n → ℕ}

theorem iterated_graph_parameter_bound (j : Selectors b r) :
    Fintype.card (ParameterIndex j)≤(∑ i,b i)*(∑ i,r i) := by
  classical
  have ht (i : Fin n) : (∑ l : {l : Fin n // i≤l},r l.val)≤∑ l,r l := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun l : Fin n => i≤l))
      (by intro l; simp) r]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Nat.zero_le _)
  calc
    Fintype.card (ParameterIndex j) =
        ∑ i,(b i-r i)*(∑ l : {l : Fin n // i≤l},r l.val) := by
      simp only [ParameterIndex,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,card_outside]
    _ ≤ ∑ i,b i*(∑ l,r l) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.mul_le_mul (Nat.sub_le _ _) (ht i)
    _ = (∑ i,b i)*(∑ l,r l) := (Finset.sum_mul ..).symm

theorem iterated_graph_parameterCount_bound (j : Selectors b r) :
    parameterCount b r≤(∑ i,b i)*(∑ i,r i) := by
  rw [← parameter_count j]
  exact iterated_graph_parameter_bound j

end Froberg
