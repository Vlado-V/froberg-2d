module

public import Froberg.OddBackgroundQuotient
public import Froberg.OddBiformDecomposition
public import Froberg.AllEvenBiformDecomposition
public import Froberg.WeightedTriangularProducts
public import Froberg.CoordinateSubmodule

@[expose] public section

/-! Weighted components preserve the literal scalar/linear background
relations. Consequently its complete odd target quotient splits into all
odd target rows, including rows not present in the coefficient source. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}

def biformParityComponent (e : ZMod 2) (t p : ℕ) (hp : p<2) (ht : t%2=p) :
    biformParitySpace K h m d e →ₗ[K] biformParitySpace K h m d (p : ZMod 2) where
  toFun v := ⟨weightedHomogeneousComponent (blockWeight h m) t v.val,⟨
    weightedComponent_preserves_homogeneous _ v.property.1 t,by
      apply (parity_homogeneous_iff (blockWeight h m) _ p hp).2
      intro a ha
      rw [(weightedHomogeneousComponent_isWeightedHomogeneous t v.val) ha,ht]⟩⟩
  map_add' v z := Subtype.ext ((weightedHomogeneousComponent (blockWeight h m) t).map_add v.val z.val)
  map_smul' c v := Subtype.ext ((weightedHomogeneousComponent (blockWeight h m) t).map_smul c v.val)

@[simp] theorem biformParityComponent_val (e : ZMod 2) (t p : ℕ) (hp : p<2) (ht : t%2=p)
    (v : biformParitySpace K h m d e) :
    (biformParityComponent e t p hp ht v).val=
      weightedHomogeneousComponent (blockWeight h m) t v.val := rfl

theorem odd_background_component_preserves
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (hQ : ∀ i,(Q i).val.IsWeightedHomogeneous (blockWeight h m) 0)
    (hF : ∀ i,(F i).val.IsWeightedHomogeneous (blockWeight h m) 1)
    (t : ℕ) (ht : t%2=1) :
    (oddBackgroundRelations Q F).map (biformParityComponent 1 t 1 (by omega) ht)≤
      oddBackgroundRelations Q F := by
  have htpos : 1≤t := by omega
  have hteven : (t-1)%2=0 := by omega
  have hq : (evenScalarOddFamily Q).range.map
      (biformParityComponent 1 t 1 (by omega) ht)≤(evenScalarOddFamily Q).range := by
    rintro _ ⟨_,⟨a,rfl⟩,rfl⟩
    refine ⟨fun i => biformParityComponent 1 t 1 (by omega) ht (a i),?_⟩
    apply Subtype.ext
    simp only [evenScalarOddFamily,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply,
      Submodule.coe_sum,biformParityComponent_val]
    change (∑ i,(Q i).val*weightedHomogeneousComponent (blockWeight h m) t (a i).val)=
      weightedHomogeneousComponent (blockWeight h m) t (∑ i,(Q i).val*(a i).val)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have he := weighted_component_mul_homogeneous (blockWeight h m) (a i).val (Q i).val t 0 (hQ i)
    simpa only [Nat.add_zero,mul_comm] using he.symm
  have hf : (privateEvenCoefficientMap F).range.map
      (biformParityComponent 1 t 1 (by omega) ht)≤(privateEvenCoefficientMap F).range := by
    rintro _ ⟨_,⟨a,rfl⟩,rfl⟩
    refine ⟨fun i => biformParityComponent 0 (t-1) 0 (by omega) hteven (a i),?_⟩
    apply Subtype.ext
    rw [privateEvenCoefficientMap_val,biformParityComponent_val,privateEvenCoefficientMap_val,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (F i).val*weightedHomogeneousComponent (blockWeight h m) (t-1) (a i).val=_
    have he := weighted_component_mul_homogeneous (blockWeight h m) (a i).val (F i).val (t-1) 1 (hF i)
    simpa only [Nat.sub_add_cancel htpos,mul_comm] using he.symm
  simpa only [oddBackgroundRelations,Submodule.map_sup] using sup_le_sup hq hf

/-- The coordinate singleton is precisely the actual weighted component. -/
theorem oddBiformCoordinates_component_single
    (v : biformParitySpace K h m d 1) (r : Fin ((d+1)/2)) :
    oddBiformCoordinatesEquiv (biformParityComponent 1 (2*r.val+1) 1 (by omega) (by omega) v)=
      Pi.single r (oddBiformCoordinatesEquiv v r) := by
  apply oddBiformCoordinatesEquiv.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [biformParityComponent_val,oddBiformCoordinatesEquiv_symm_val]
  rw [Finset.sum_eq_single r]
  · simpa using (oddBiformCoordinatesEquiv_component v r).symm
  · intro s _ hsr
    rw [Pi.single_eq_of_ne hsr,map_zero]
  · simp

def oddBackgroundBlockRelations
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) : Submodule K (OddBiformCoordinates K h m (2*d)) :=
  (oddBackgroundRelations Q F).map oddBiformCoordinatesEquiv.toLinearMap

theorem oddBackgroundBlockRelations_single
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (hQ : ∀ i,(Q i).val.IsWeightedHomogeneous (blockWeight h m) 0)
    (hF : ∀ i,(F i).val.IsWeightedHomogeneous (blockWeight h m) 1) :
    ∀ x∈oddBackgroundBlockRelations Q F,∀ r,Pi.single r (x r)∈oddBackgroundBlockRelations Q F := by
  rintro _ ⟨v,hv,rfl⟩ r
  refine ⟨biformParityComponent 1 (2*r.val+1) 1 (by omega) (by omega) v,?_,?_⟩
  · exact odd_background_component_preserves Q F hQ hF _ (by omega) ⟨v,hv,rfl⟩
  · exact oddBiformCoordinates_component_single v r

abbrev OddTargetBlock (K : Type) [Field K] (h m d : ℕ) (r : Fin ((2*d+1)/2)) :=
  Forms K h (2*r.val+1) ⊗[K] Forms K m (2*d-(2*r.val+1))

instance oddTargetBlockGroup (K : Type) [Field K] (h m d : ℕ)
    (r : Fin ((2*d+1)/2)) : AddCommGroup (OddTargetBlock K h m d r) :=
  tensorFormGroup

instance oddTargetBlockModule (K : Type) [Field K] (h m d : ℕ)
    (r : Fin ((2*d+1)/2)) : Module K (OddTargetBlock K h m d r) :=
  TensorProduct.leftModule

def oddBackgroundBlocksEquiv
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (hQ : ∀ i,(Q i).val.IsWeightedHomogeneous (blockWeight h m) 0)
    (hF : ∀ i,(F i).val.IsWeightedHomogeneous (blockWeight h m) 1) :
    (biformParitySpace K h m (2*d) 1 ⧸ oddBackgroundRelations Q F) ≃ₗ[K]
      ((r : Fin ((2*d+1)/2)) →
        (OddTargetBlock K h m d r ⧸
          coordinateRelation (oddBackgroundBlockRelations Q F) r)) :=
  (Submodule.Quotient.equiv _ _ (oddBiformCoordinatesEquiv (K := K) (h := h) (m := m) (d := 2*d)) rfl).trans
    (coordinateQuotientEquiv _ (oddBackgroundBlockRelations_single Q F hQ hF))

end Froberg
