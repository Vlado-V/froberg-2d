module

public import Froberg.PreparedZeroLayers
public import Froberg.HigherCapacityParameters
public import Froberg.CapacityRelabel

@[expose] public section

/-! The induction includes every positive even degree. Inactive layers
have zero slots and do not change the scalar count or the actual family. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Filter
open scoped Topology

def allEvenIndices (d : ℕ) : Finset ℕ :=
  (Finset.range (d+1)).filter (fun j => 2≤j ∧ j%2=0)

theorem mem_allEvenIndices {d j : ℕ} : j∈allEvenIndices d ↔ 2≤j ∧ j≤d ∧ j%2=0 := by
  simp only [allEvenIndices,Finset.mem_filter,Finset.mem_range]
  omega

theorem activeEven_subset_allEven {d : ℕ} (hd : 3≤d) :
    activeEvenIndices d⊆allEvenIndices d := by
  intro j hj
  obtain ⟨hj2,hjd,hje⟩ := activeEvenIndices_bounds hd hj
  exact mem_allEvenIndices.mpr ⟨hj2,hjd.le,Nat.even_iff.mp hje⟩

def allEvenCount (d h n e j : ℕ) : ℕ :=
  if j∈activeEvenIndices d then targetLayerCount d h n e j else 0

@[simp] theorem allEvenCount_active {d j : ℕ} (h n e : ℕ) (hj : j∈activeEvenIndices d) :
    allEvenCount d h n e j=targetLayerCount d h n e j := by
  simp only [allEvenCount,if_pos hj]

@[simp] theorem allEvenCount_inactive {d j : ℕ} (h n e : ℕ) (hj : j∉activeEvenIndices d) :
    allEvenCount d h n e j=0 := by simp only [allEvenCount,if_neg hj]

def allEvenLabelEquiv {d : ℕ} (hd : 3≤d) (q h n e : ℕ) :
    Label q (activeEvenIndices d) (targetLayerCount d h n e) ≃
      Label q (allEvenIndices d) (allEvenCount d h n e) :=
  zeroLabelEquiv (activeEven_subset_allEven hd)
    (fun j hj => (allEvenCount_active h n e hj).symm)
    (fun j _ hj => allEvenCount_inactive h n e hj)

theorem allEvenLabel_card {d : ℕ} (hd : 3≤d) (q h n e : ℕ) :
    Fintype.card (Label q (allEvenIndices d) (allEvenCount d h n e))=
      Fintype.card (Label q (activeEvenIndices d) (targetLayerCount d h n e)) :=
  (Fintype.card_congr (allEvenLabelEquiv hd q h n e)).symm

theorem allEvenLabel_count_limit {d : ℕ} (hd : 3≤d) (h extra : ℕ)
    (e : ℕ → ℕ)
    (he : ∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2)) :
    Tendsto (fun n : ℕ =>
      (Fintype.card (Label (upperCount n d) (allEvenIndices d)
        (allEvenCount d h n (e n+extra))) : ℝ)/(n : ℝ)^d)
      atTop (𝓝 (criticalRatio d/(d.factorial : ℝ))) := by
  simpa only [allEvenLabel_card hd] using targetLayerLabel_count_limit hd h extra e he

end Froberg.PreparedParameters
