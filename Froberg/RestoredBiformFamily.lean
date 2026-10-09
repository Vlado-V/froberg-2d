module

public import Froberg.PreparedFamilyIndependence
public import Froberg.PreparedRestoredRelations
public import Froberg.FilteredEvenOddExact

@[expose] public section

/-! The restored family has arbitrary positive even components but its
scalar component remains exactly the original scalar parameter. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q r : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def restoredBiformFamily (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredSpace m d q J counts O) (i : Fin r) : biformParitySpace K h m d 0 :=
  ⟨(restoredFamilyLinear hd hO hJ heven idx slot p i).val,
    (restoredFamilyLinear hd hO hJ heven idx slot p i).property.1,
    (parity_homogeneous_iff (blockWeight h m) _ 0 (by decide)).mpr
      ((mem_weightedParitySpace_iff _ _ _).mp
        (restoredFamilyLinear hd hO hJ heven idx slot p i).property.2)⟩

theorem pureShift_weight (hd : d%2=0)
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (U : Fin (finrank K (Forms K h d)) → Forms K h d) (i : Fin r) :
    (PolynomialRestoration.pureShift (pureEvenEmbed hd) slot U i).val.IsWeightedHomogeneous
      (blockWeight h m) d := by
  classical
  simp only [PolynomialRestoration.pureShift,LinearMap.sum_apply,Finset.sum_apply,
    LinearMap.comp_apply,LinearMap.proj_apply,Submodule.coe_sum]
  apply (weightedHomogeneousSubmodule K (blockWeight h m) d).sum_mem
  intro k _
  by_cases hk : i=slot k
  · subst i
    simp only [LinearMap.single_apply,Pi.single_eq_same]
    exact rename_weightedHomogeneous
      (⟨Sum.inl,Sum.inl_injective⟩ : Fin h ↪ Fin h ⊕ Fin m)
      (fun _ => 1) (blockWeight h m) (fun _ => rfl) (U k).property
  · simp only [LinearMap.single_apply,Pi.single_eq_of_ne hk,Submodule.coe_zero]
    exact (weightedHomogeneousSubmodule K (blockWeight h m) d).zero_mem

theorem restoredBiformFamily_scalar_component (hdp : 0<d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hpos : ∀ j∈J,0<j)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredSpace m d q J counts O) (i : Fin r) :
    weightedHomogeneousComponent (blockWeight h m) 0
      (restoredBiformFamily hd hO hJ heven idx slot p i).val=
        rename Sum.inr (p.1.1 (idx i)).val := by
  change weightedHomogeneousComponent (blockWeight h m) 0
    (generator p.1 (idx i)+(PolynomialRestoration.pureShift (pureEvenEmbed hd) slot p.2 i).val)=_
  rw [map_add,PreparedTarget.prepared_generator_component_zero hO hpos,
    weightedHomogeneousComponent_of_mem (pureShift_weight hd slot p.2 i),if_neg (by omega),add_zero]
  rfl

end Froberg.PreparedParameters
