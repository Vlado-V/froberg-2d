module

public import Froberg.FilteredOddElimination
public import Froberg.PreparedOddVectorCriteria

@[expose] public section

/-! All even higher components, including the restored pure terms, are
allowed in the full odd row once the scalar and vector rows are exact. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial Quartic VectorMultiplicationCoordinates
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}

theorem filtered_even_odd_exact (hd : 3≤d)
    (A : Fin q → biformParitySpace K h m d 0)
    (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1))
    (hzero : ∀ i,weightedHomogeneousComponent (blockWeight h m) 0 (A i).val=
      rename Sum.inr (Q i).val)
    (hfirst : FirstVectorRowExact Q g) (hhigher : HigherOddRows Q g) :
    OddSplitExact A (fun i => linearOddForm (by omega) (g i)) := by
  intro c v hcycle
  let a : Fin q → MvPolynomial (Fin h ⊕ Fin m) K := fun i => rename Sum.inr (Q i).val
  let E := fun i => (A i).val-a i
  let O := fun k => (linearOddForm (by omega : 1≤d) (g k)).val
  have ha (i) : (a i).IsHomogeneous d ∧ (a i).IsWeightedHomogeneous (blockWeight h m) 0 := by
    refine ⟨(Q i).property.rename_isHomogeneous,?_⟩
    exact rename_weightedHomogeneous
      (⟨Sum.inr,Sum.inr_injective⟩ : Fin m ↪ Fin h ⊕ Fin m)
      (fun _ => 0) (blockWeight h m) (fun _ => rfl) (weightedHomogeneous_zero_weight (Q i).val)
  have hE (i) : (E i).IsHomogeneous d ∧ E i∈weightedParitySpace (blockWeight h m) 0 := by
    refine ⟨(A i).property.1.sub (ha i).1,?_⟩
    apply (weightedParitySpace (blockWeight h m) 0).sub_mem
    · exact (mem_weightedParitySpace_iff _ _ _).mpr
        ((parity_homogeneous_iff (blockWeight h m) (A i).val 0 (by decide)).mp (A i).property.2)
    · exact IsWeightedHomogeneous.mem_parity (ha i).2 rfl
  have hEzero (i) : weightedHomogeneousComponent (blockWeight h m) 0 (E i)=0 := by
    rw [show E i=(A i).val-a i from rfl,map_sub,hzero,
      weightedHomogeneousComponent_of_mem (ha i).2,if_pos rfl,sub_self]
  have hO (k) : (O k).IsHomogeneous d ∧ (O k).IsWeightedHomogeneous (blockWeight h m) 1 := by
    refine ⟨(linearOddForm (by omega : 1≤d) (g k)).property.1,?_⟩
    exact biformImage_output_weight (Forms K h 1) (Forms K m (d-1)) le_rfl
      (sumBiformMap_range.le ⟨linearOutputTensorEquiv (g k),rfl⟩)
  have hsum (i) : a i+E i=(A i).val := by dsimp [E]; abel
  obtain ⟨B,hB,hB'⟩ := filtered_odd_cycles (blockWeight h m)
    (by intro x; cases x <;> simp [blockWeight]) d hd a E (fun i => (c i).val)
    O (fun _ => 0) (fun i => (v i).val) ha hE hEzero hO
    (fun _ => ⟨isHomogeneous_zero _ _ _,(weightedHomogeneousSubmodule K _ _).zero_mem⟩)
    (Or.inr (fun _ => rfl)) (fun i => (c i).property.1) (fun i => (v i).property.1)
    (fun i => (parity_homogeneous_iff (blockWeight h m) (c i).val 1 (by decide)).mp (c i).property.2)
    (fun i => (parity_homogeneous_iff (blockWeight h m) (v i).val 0 (by decide)).mp (v i).property.2)
    (bottom_polynomial_constants_of_exact (by omega) Q g hfirst) hhigher
    (by simpa only [hsum,add_zero,O] using hcycle)
  exact ⟨B,by simpa only [add_zero,O] using hB,by simpa only [hsum] using hB'⟩

end Froberg
