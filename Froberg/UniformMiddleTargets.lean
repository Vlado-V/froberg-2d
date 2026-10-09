module

public import Froberg.UniformTargetConvolution
public import Froberg.MiddleRowsCommonOpen

@[expose] public section

/-! Numerical target-row bounds followed by the common open over each infinite field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Froberg
open Module MvPolynomial Filter Quartic
open scoped Topology
universe u
attribute [local instance] tensorGroup

theorem eventually_target_row_from_prefix_uniform {d j b : ℕ} (hj : 0 < j) (hjd : j < d)
    (hjb : j≤b) (hbj : b<2*j) (hbd : b≤d+j) (α : ℝ) (hα : targetCost d j b < α) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop, ∀ (K : Type u) [Field K] [Infinite K],
      ∃ (o : Fin ⌈α*(h : ℝ)^j*(m : ℝ)^(d-j)⌉₊ → Forms K h j)
        (f : Fin ⌈α*(h : ℝ)^j*(m : ℝ)^(d-j)⌉₊ → Forms K m (d-j)),
        Function.Surjective (biformFamilyMap (x := b-j) (y := d+j-b) o f) := by
  apply eventually_middle_biform_surjective_uniform hj (by omega) (by omega) α
  rwa [convolutionOutputThreshold_targetCost hjd.le hjb hbd]

theorem eventually_higher_target_row_uniform {d b : ℕ} (hd : 3 ≤ d) (hb : 5 ≤ b)
    (hbd : b ≤ d) (hcut : b < d ∨ Odd d) :
    ∃ j ∈ activeHigherIndices d, j < b ∧ b < 2*j ∧
      ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop, ∀ (K : Type u) [Field K] [Infinite K],
        ∃ (o : Fin ⌈(101/100 : ℝ)*higherCountGamma d j*(h : ℝ)^j*(m : ℝ)^(d-j)⌉₊ → Forms K h j)
          (f : Fin ⌈(101/100 : ℝ)*higherCountGamma d j*(h : ℝ)^j*(m : ℝ)^(d-j)⌉₊ → Forms K m (d-j)),
          Function.Surjective (biformFamilyMap (x := b-j) (y := d+j-b) o f) := by
  obtain ⟨j,hj,hjb,hbj,hcost⟩ := higher_layers_cover_targets hd hb hbd hcut
  refine ⟨j,hj,hjb,hbj,?_⟩
  exact eventually_target_row_from_prefix_uniform (by omega) (by omega) hjb.le hbj (by omega) _ hcost

theorem eventually_middle_rows_common_open_uniform {d : ℕ} (hd : 3≤d) :
    ∃ layer : MiddleTargetIndex d → HigherLayerIndex d,
      (∀ b,(layer b).val<b.val.val ∧ b.val.val<2*(layer b).val) ∧
      ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop, ∀ (K : Type u) [Field K] [Infinite K],
        ∃ D : MvPolynomial (Fin (finrank K (BiformLayerFamily K h m
          (fun j : HigherLayerIndex d => j.val) (fun j => d-j.val)
          (fun j => higherGeneratorCount d h m j.val)))) K,
          (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 → ∀ b : MiddleTargetIndex d,
            Function.Surjective (biformTensorFamilyMap
              (x := b.val.val-(layer b).val) (y := d+(layer b).val-b.val.val)
              (((Module.finBasis K (BiformLayerFamily K h m
                (fun j : HigherLayerIndex d => j.val) (fun j => d-j.val)
                (fun j => higherGeneratorCount d h m j.val))).equivFun.symm a) (layer b))) := by
  classical
  have hex (b : MiddleTargetIndex d) := eventually_higher_target_row_uniform hd b.property.1
    (Nat.le_of_lt_succ b.val.isLt) b.property.2
  choose j hj hjb hbj hrow using hex
  let layer : MiddleTargetIndex d → HigherLayerIndex d := fun b => ⟨j b,hj b⟩
  refine ⟨layer,fun b => ⟨hjb b,hbj b⟩,?_⟩
  have houter := Filter.eventually_all.mpr hrow
  filter_upwards [houter] with h hh
  have hinner := Filter.eventually_all.mpr hh
  filter_upwards [hinner] with m hm
  intro K _ _
  apply biform_layers_common_open_of_pure (K := K) (h := h) (m := m)
    (fun j : HigherLayerIndex d => j.val) (fun j => d-j.val)
    (fun j => higherGeneratorCount d h m j.val) layer
    (fun b => b.val.val-(layer b).val) (fun b => d+(layer b).val-b.val.val)
  intro b
  convert hm b K using 1 <;> simp only [higherGeneratorCount,layer]

end Froberg
