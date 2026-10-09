module

public import Froberg.BiformSplitEndpoint
public import Froberg.FilteredFamilyIndependence
public import Froberg.PreparedIndependenceOpen

@[expose] public section

/-! Independence of a split endpoint is detected by its scalar and
linear components. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial VectorMultiplicationCoordinates
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}

theorem biformSplitEndpoint_independent
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (hQ : LinearIndependent K (fun i => weightedHomogeneousComponent (blockWeight h m) 0 (Q i).val))
    (hF : LinearIndependent K (fun i => weightedHomogeneousComponent (blockWeight h m) 1 (F i).val))
    (hFzero : ∀ i,weightedHomogeneousComponent (blockWeight h m) 0 (F i).val=0) :
    LinearIndependent K (biformSplitEndpoint Q F) := by
  have hfull := two_step_linearIndependent (fun i => (Q i).val) (fun i => (F i).val)
    (weightedHomogeneousComponent (blockWeight h m) 0)
    (weightedHomogeneousComponent (blockWeight h m) 1) hQ hF hFzero
  let idx : Fin q ⊕ Fin f ≃ Fin (q+f) := finSumFinEquiv
  have hh := hfull.comp idx.symm idx.symm.injective
  have hrename := hh.map' (rename finSumFinEquiv).toLinearMap
    (LinearMap.ker_eq_bot.mpr (renameEquiv K finSumFinEquiv).injective)
  apply LinearIndependent.of_comp (Forms K (h+m) d).subtype
  convert hrename using 1
  funext k
  obtain ⟨i,rfl⟩ := idx.surjective k
  simp only [Function.comp_apply,AlgHom.toLinearMap_apply,Equiv.symm_apply_apply]
  have hback := biformSplitEndpoint_back Q F i
  have hh := congrArg (rename finSumFinEquiv) hback
  have hcancel (z : Poly K (h+m)) : rename finSumFinEquiv (rename finSumFinEquiv.symm z)=z :=
    (renameEquiv K finSumFinEquiv).right_inv z
  rw [hcancel] at hh
  exact hh

theorem linearOddForm_component (hd : 1≤d) (g : Rows K h m (d-1)) (b : ℕ) :
    weightedHomogeneousComponent (blockWeight h m) b (linearOddForm hd g).val=
      if b=1 then (linearOddForm hd g).val else 0 := by
  have hh : (linearOddForm hd g).val.IsWeightedHomogeneous (blockWeight h m) 1 :=
    biformImage_output_weight _ _ le_rfl (PreparedTarget.outerVectorEquiv g).property
  exact weightedHomogeneousComponent_of_mem hh

theorem linearOddForm_independent (hd : 1≤d) (g : Fin f → Rows K h m (d-1))
    (hg : LinearIndependent K g) : LinearIndependent K (fun i => (linearOddForm hd (g i)).val) := by
  have h₁ := hg.map' (PreparedTarget.outerVectorEquiv (K := K) (h := h) (m := m) (d := d)).toLinearMap
    (LinearMap.ker_eq_bot.mpr PreparedTarget.outerVectorEquiv.injective)
  exact h₁.map' (biformImage (Forms K h 1) (Forms K m (d-1))).subtype (Submodule.ker_subtype _)

end Froberg
