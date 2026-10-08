import Froberg.BiformLayerOpen
import Froberg.MiddleTargetCoverage

/-! The prescribed higher generator layers fill every middle target row
simultaneously, with a single family in each active layer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Froberg
open Module MvPolynomial Filter Quartic
open scoped Topology
variable {K : Type*} [Field K] [Infinite K]
attribute [local instance] tensorGroup

abbrev MiddleTargetIndex (d : ℕ) := {b : Fin (d+1) // 5≤b.val ∧ (b.val<d ∨ Odd d)}
abbrev HigherLayerIndex (d : ℕ) := {j : ℕ // j∈activeHigherIndices d}

theorem eventually_middle_rows_common_open {d : ℕ} (hd : 3≤d) :
    ∃ layer : MiddleTargetIndex d → HigherLayerIndex d,
      (∀ b,(layer b).val<b.val.val ∧ b.val.val<2*(layer b).val) ∧
      ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
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
  have hex (b : MiddleTargetIndex d) := eventually_higher_target_row (K := K) hd b.property.1
    (Nat.le_of_lt_succ b.val.isLt) b.property.2
  choose j hj hjb hbj hrow using hex
  let layer : MiddleTargetIndex d → HigherLayerIndex d := fun b => ⟨j b,hj b⟩
  refine ⟨layer,fun b => ⟨hjb b,hbj b⟩,?_⟩
  have houter := Filter.eventually_all.mpr hrow
  filter_upwards [houter] with h hh
  have hinner := Filter.eventually_all.mpr hh
  filter_upwards [hinner] with m hm
  apply biform_layers_common_open_of_pure (K := K) (h := h) (m := m)
    (fun j : HigherLayerIndex d => j.val) (fun j => d-j.val)
    (fun j => higherGeneratorCount d h m j.val) layer
    (fun b => b.val.val-(layer b).val) (fun b => d+(layer b).val-b.val.val)
  intro b
  convert hm b using 1 <;> simp only [higherGeneratorCount,layer]

end Froberg
