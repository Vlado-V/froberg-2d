import Froberg.PreparedEndpointParity
import Froberg.FilteredFamilyIndependence

/-! Independence of the scalar and linear leading parts implies
independence of the entire prepared family, for arbitrary higher parts. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem prepared_generator_component_zero
    (hO : ∀ j∈J,O j≤Forms K h j) (hpos : ∀ j∈J,0<j)
    (p : PreparedParameters.Space m d q J counts O) (i : PreparedParameters.Label q J counts) :
    weightedHomogeneousComponent (blockWeight h m) 0 (PreparedParameters.generator p i)=
      PreparedParameters.scalar p i := by
  have hs : (PreparedParameters.scalar p i).IsWeightedHomogeneous (blockWeight h m) 0 :=
    PreparedParameters.scalar_weight p i
  rw [PreparedParameters.generator,map_add,weightedHomogeneousComponent_of_mem hs,if_pos rfl]
  suffices weightedHomogeneousComponent (blockWeight h m) 0 (PreparedParameters.high p i)=0 by
    rw [this,add_zero]
  cases i with
  | inl i => exact map_zero _
  | inr i =>
    have hh : (PreparedParameters.high p (Sum.inr i)).IsWeightedHomogeneous (blockWeight h m) i.1.val :=
      PreparedParameters.high_weight hO p (Sum.inr i)
    rw [weightedHomogeneousComponent_of_mem hh]
    exact if_neg (by have := hpos _ i.1.property; change ¬0=i.1.val; omega)

theorem combinedLinear_weight (P : OuterSpace K (Fin h) m d u) (F : OuterSpace K (Fin h) m d f)
    (k : Fin f ⊕ Fin u) : (combinedLinear P F k).IsWeightedHomogeneous (blockWeight h m) 1 := by
  cases k with
  | inl i => exact biformImage_output_weight _ _ le_rfl (F i).property
  | inr i => exact biformImage_output_weight _ _ le_rfl (P i).property

theorem combinedPure_weight (U : Fin u → Forms K h d) (k : Fin f ⊕ Fin u) :
    (combinedPure U k).IsWeightedHomogeneous (blockWeight h m) d := by
  cases k with
  | inl i => exact (weightedHomogeneousSubmodule K _ _).zero_mem
  | inr i =>
    exact rename_weightedHomogeneous
      (⟨Sum.inl,Sum.inl_injective⟩ : Fin h ↪ Fin h ⊕ Fin m)
      (fun _ => 1) (blockWeight h m) (fun _ => rfl) (U i).property

theorem oddGenerator_component_zero (hd : 0<d) (U : Fin u → Forms K h d)
    (P : OuterSpace K (Fin h) m d u) (F : OuterSpace K (Fin h) m d f) (k : Fin f ⊕ Fin u) :
    weightedHomogeneousComponent (blockWeight h m) 0 (oddGenerator U P F k)=0 := by
  change weightedHomogeneousComponent (blockWeight h m) 0 (combinedLinear P F k+combinedPure U k)=0
  rw [map_add,weightedHomogeneousComponent_of_mem (combinedLinear_weight P F k),
    weightedHomogeneousComponent_of_mem (combinedPure_weight U k),if_neg (by omega),
    if_neg (by omega),zero_add]

theorem oddGenerator_component_one (hd : 1<d) (U : Fin u → Forms K h d)
    (P : OuterSpace K (Fin h) m d u) (F : OuterSpace K (Fin h) m d f) (k : Fin f ⊕ Fin u) :
    weightedHomogeneousComponent (blockWeight h m) 1 (oddGenerator U P F k)=combinedLinear P F k := by
  change weightedHomogeneousComponent (blockWeight h m) 1 (combinedLinear P F k+combinedPure U k)=_
  rw [map_add,weightedHomogeneousComponent_of_mem (combinedLinear_weight P F k),
    weightedHomogeneousComponent_of_mem (combinedPure_weight U k),if_pos rfl,
    if_neg (by omega),add_zero]

theorem prepared_family_independent (hd : 1<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (hpos : ∀ j∈J,0<j)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (p : PreparedParameters.Space m d q J counts O × OuterSpace K (Fin h) m d f)
    (hscalar : LinearIndependent K p.1.1) (hlinear : LinearIndependent K (combinedLinear P p.2)) :
    LinearIndependent K (zeroScalarEndpointFamily (by omega) hO hJ U P p) := by
  have hs : LinearIndependent K (PreparedParameters.scalar p.1) := by
    apply (hscalar.map' (Forms K m d).subtype (Submodule.ker_subtype _)).map'
      (rename Sum.inr).toLinearMap
    exact LinearMap.ker_eq_bot.mpr (rename_injective _ Sum.inr_injective)
  have hfull := two_step_linearIndependent (PreparedParameters.generator p.1) (oddGenerator U P p.2)
    (weightedHomogeneousComponent (blockWeight h m) 0)
    (weightedHomogeneousComponent (blockWeight h m) 1)
    (by simpa only [prepared_generator_component_zero hO hpos] using hs)
    (by simpa only [oddGenerator_component_one hd] using hlinear)
    (oddGenerator_component_zero (by omega) U P p.2)
  let idx := Fintype.equivFin (Label q f u J counts)
  have hh := hfull.comp idx.symm idx.symm.injective
  have hrename := hh.map' (rename finSumFinEquiv).toLinearMap
    (LinearMap.ker_eq_bot.mpr (renameEquiv K finSumFinEquiv).injective)
  apply LinearIndependent.of_comp (Forms K (h+m) d).subtype
  convert hrename using 1
  funext k
  obtain ⟨i,rfl⟩ := idx.surjective k
  simp only [Function.comp_apply,AlgHom.toLinearMap_apply,Equiv.symm_apply_apply]
  have hback := zeroScalarEndpointFamily_back (by omega : 0<d) hO hJ U P p i
  have hh := congrArg (rename finSumFinEquiv) hback
  have hcancel (z : Poly K (h+m)) : rename finSumFinEquiv (rename finSumFinEquiv.symm z)=z :=
    (renameEquiv K finSumFinEquiv).right_inv z
  rw [hcancel] at hh
  exact hh

end Froberg.PreparedTarget
