import Froberg.StrictVectorModel

/-! Injection in the largest coefficient degree implies all smaller degrees. -/
noncomputable section
namespace Froberg.VectorExpansionOpen
open Module MvPolynomial VectorMultiplicationCoordinates Quartic
variable {K : Type*} [Field K] {h n s d t c : ℕ}

lemma vector_lower_injection (hn : 0 < n) (ht : t ≤ d) (g : Fin c → Rows K h n s)
    (hi : Function.Injective (BilinearImage.tupleMap (multiplication (d := d)) g)) :
    Function.Injective (BilinearImage.tupleMap (multiplication (d := t)) g) := by
  classical
  suffices hz : ∀ a : Fin c → Forms K n t,
      BilinearImage.tupleMap (multiplication (d := t)) g a=0 → a=0 by
    intro a b hab
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub,hab,sub_self]
  intro a ha
  let m : Poly K n := monomial (Finsupp.single (⟨0,hn⟩ : Fin n) (d-t)) 1
  have hm : m.IsHomogeneous (d-t) := isHomogeneous_monomial 1 (by rw [Finsupp.degree_single])
  have hm0 : m ≠ 0 := by simp [m]
  let b : Fin c → Forms K n d := fun i => ⟨m*(a i).val,by
    simpa only [Forms,mem_homogeneousSubmodule,Nat.sub_add_cancel ht] using hm.mul (a i).property⟩
  have hb : BilinearImage.tupleMap (multiplication (d := d)) g b=0 := by
    funext j
    apply Subtype.ext
    have haj := congrArg (fun x : Rows K h n (s+t) => (x j).val) ha
    simp only [BilinearImage.tupleMap_apply,Finset.sum_apply,Submodule.coe_sum,
      multiplication_val,Pi.zero_apply,Submodule.coe_zero] at haj ⊢
    change (∑ i,(m*(a i).val)*(g i j).val)=0
    rw [show (∑ i,(m*(a i).val)*(g i j).val)=m*(∑ i,(a i).val*(g i j).val) by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
    rw [haj,mul_zero]
  have hb0 : b=0 := hi (hb.trans (map_zero _).symm)
  funext i
  apply Subtype.ext
  have hh := congrArg (fun x : Fin c → Forms K n d => (x i).val) hb0
  change m*(a i).val=0 at hh
  exact (mul_eq_zero.mp hh).resolve_left hm0

lemma StrictModel.lower_injective {g : Fin c → Rows K h n s} {G : ℝ}
    (hg : StrictModel g d G) (hn : 0 < n) (ht : t ≤ d) :
    Function.Injective (BilinearImage.tupleMap (multiplication (d := t)) g) :=
  vector_lower_injection hn ht g hg.product_injective

end Froberg.VectorExpansionOpen
