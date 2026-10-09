module

public import Froberg.ComponentQuotientIndependence
public import Froberg.PreparedFamilyIndependence

@[expose] public section

/-! Positive prepared generators remain independent modulo the entire
scalar polynomial subspace. Pure top-degree perturbations are arbitrary. -/
noncomputable section
set_option maxHeartbeats 250000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def positivePerturbedFamily (p : Space m d q J counts O)
    (U : ProductRows.LayerLabel J counts → MvPolynomial (Fin h ⊕ Fin m) K)
    (i : ProductRows.LayerLabel J counts) : MvPolynomial (Fin h ⊕ Fin m) K :=
  generator p (Sum.inr i)+U i

theorem positivePerturbedFamily_component
    (hO : ∀ j∈J,O j≤Forms K h j) (hpos : ∀ j∈J,0<j) (hJ : ∀ j∈J,0<counts j → j<d)
    (p : Space m d q J counts O)
    (U : ProductRows.LayerLabel J counts → MvPolynomial (Fin h ⊕ Fin m) K)
    (hU : ∀ i,(U i).IsWeightedHomogeneous (blockWeight h m) d)
    (j k : J) (i : Fin (counts k.val)) (hj : 0<counts j.val) :
    weightedHomogeneousComponent (blockWeight h m) j.val (positivePerturbedFamily p U ⟨k,i⟩)=
      if k=j then (p.2 k i).val else 0 := by
  have hs : (scalar p (Sum.inr ⟨k,i⟩)).IsWeightedHomogeneous (blockWeight h m) 0 :=
    scalar_weight p _
  have he : (high p (Sum.inr ⟨k,i⟩)).IsWeightedHomogeneous (blockWeight h m) k.val :=
    high_weight hO p _
  rw [positivePerturbedFamily,map_add,generator,map_add,
    weightedHomogeneousComponent_of_mem hs,if_neg (by have := hpos _ j.property;omega),
    zero_add,weightedHomogeneousComponent_of_mem he,
    weightedHomogeneousComponent_of_mem (hU _),if_neg (ne_of_lt (hJ _ j.property hj)),add_zero]
  by_cases hk : k=j
  · subst k
    simp only [ite_true]
    rfl
  · rw [if_neg (fun h => hk (Subtype.ext h.symm)),if_neg hk]

theorem positivePerturbedFamily_scalar_independent
    (hO : ∀ j∈J,O j≤Forms K h j) (hpos : ∀ j∈J,0<j) (hJ : ∀ j∈J,0<counts j → j<d)
    (p : Space m d q J counts O)
    (hp : ∀ j,LinearIndependent K (p.2 j))
    (U : ProductRows.LayerLabel J counts → MvPolynomial (Fin h ⊕ Fin m) K)
    (hU : ∀ i,(U i).IsWeightedHomogeneous (blockWeight h m) d) :
    LinearIndependent K (fun i => (weightedHomogeneousSubmodule K (blockWeight h m) 0).mkQ
      (positivePerturbedFamily p U i)) := by
  apply component_quotient_family_independent _ (fun j i => (p.2 j i).val)
  · intro j _ a ha
    rw [weightedHomogeneousComponent_of_mem ha,if_neg (by have := hpos _ j.property;omega)]
  · exact positivePerturbedFamily_component hO hpos hJ p U hU
  · intro j
    exact (hp j).map' (biformImage (O j.val) (Forms K m (d-j.val))).subtype
      (Submodule.ker_subtype (biformImage (O j.val) (Forms K m (d-j.val))))

theorem positivePerturbedFamily_component_one (hd : 1<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hmin : ∀ j∈J,2≤j)
    (p : Space m d q J counts O)
    (U : ProductRows.LayerLabel J counts → MvPolynomial (Fin h ⊕ Fin m) K)
    (hU : ∀ i,(U i).IsWeightedHomogeneous (blockWeight h m) d)
    (i : ProductRows.LayerLabel J counts) :
    weightedHomogeneousComponent (blockWeight h m) 1 (positivePerturbedFamily p U i)=0 := by
  have hs : (scalar p (Sum.inr i)).IsWeightedHomogeneous (blockWeight h m) 0 := scalar_weight p _
  have he : (high p (Sum.inr i)).IsWeightedHomogeneous (blockWeight h m) i.1.val := high_weight hO p _
  rw [positivePerturbedFamily,map_add,generator,map_add,
    weightedHomogeneousComponent_of_mem hs,if_neg (by decide),
    weightedHomogeneousComponent_of_mem he,if_neg (by have := hmin _ i.1.property;omega),
    weightedHomogeneousComponent_of_mem (hU _),if_neg (by omega),zero_add,zero_add]

theorem positive_private_scalar_independent (hd : 1<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hmin : ∀ j∈J,2≤j) (hJ : ∀ j∈J,0<counts j → j<d)
    (p : Space m d q J counts O) (hp : ∀ j,LinearIndependent K (p.2 j))
    (U : ProductRows.LayerLabel J counts → MvPolynomial (Fin h ⊕ Fin m) K)
    (hU : ∀ i,(U i).IsWeightedHomogeneous (blockWeight h m) d)
    (P W : Fin u → MvPolynomial (Fin h ⊕ Fin m) K)
    (hP : ∀ i,(P i).IsWeightedHomogeneous (blockWeight h m) 1)
    (hW : ∀ i,(W i).IsWeightedHomogeneous (blockWeight h m) d)
    (hPi : LinearIndependent K P) :
    LinearIndependent K (fun i : ProductRows.LayerLabel J counts ⊕ Fin u =>
      (weightedHomogeneousSubmodule K (blockWeight h m) 0).mkQ
        (Sum.elim (positivePerturbedFamily p U) (fun k => P k+W k) i)) := by
  apply quotient_split_independent _ _ _ (weightedHomogeneousComponent (blockWeight h m) 1)
  · intro a ha
    change weightedHomogeneousComponent (blockWeight h m) 1 a=0
    rw [weightedHomogeneousComponent_of_mem ha,if_neg (by decide)]
  · exact positivePerturbedFamily_scalar_independent hO
      (fun j hj => by have := hmin j hj;omega) hJ p hp U hU
  · have hcomp (i) : weightedHomogeneousComponent (blockWeight h m) 1 (P i+W i)=P i := by
      rw [map_add,weightedHomogeneousComponent_of_mem (hP i),if_pos rfl,
        weightedHomogeneousComponent_of_mem (hW i),if_neg (by omega),add_zero]
    simpa only [hcomp] using hPi
  · exact positivePerturbedFamily_component_one hd hO hmin p U hU

end Froberg.PreparedParameters
