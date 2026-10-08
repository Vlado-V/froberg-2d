import Froberg.OddRelativeDimensions

/-! Actual affine scalar motion in the remaining even generators. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u e : ℕ}

def oddEvenAffineFamily (E : Fin e → biformParitySpace K h m d 0)
    (a : Fin e → Forms K m d) : Fin e → biformParitySpace K h m d 0 :=
  fun i => E i+scalarEvenBiform (a i)

def oddEvenAffineRelations
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) (a : Fin e → Forms K m d) :=
  (oddEvenRelativeMap Q F G (oddEvenAffineFamily E a)).range

theorem oddEvenRelativeMap_single
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) (i : Fin e)
    (v : biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F G) :
    oddEvenRelativeMap Q F G E (Pi.single i v)=oddBackgroundQuotientProduct Q F G (E i) v := by
  classical
  rw [oddEvenRelativeMap_apply,Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji,map_zero]
  · simp

theorem oddEvenAffineRelations_generator_mem
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) (a : Fin e → Forms K m d) (i : Fin e)
    (v : biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F G) :
    oddBackgroundScalarProduct Q F G (a i) v+oddBackgroundQuotientProduct Q F G (E i) v∈
      oddEvenAffineRelations Q F G E a := by
  refine ⟨Pi.single i v,?_⟩
  rw [oddEvenRelativeMap_single]
  change oddBackgroundQuotientProduct Q F G (E i+scalarEvenBiform (a i)) v=_
  rw [map_add,LinearMap.add_apply,add_comm]
  rfl

theorem oddEvenAffineRelations_finrank
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) (a : Fin e → Forms K m d)
    (hi : Function.Injective (oddEvenRelativeMap Q F G (oddEvenAffineFamily E a))) :
    finrank K ((biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q F G) ⧸
      oddEvenAffineRelations Q F G E a)=
      finrank K (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q F G)-
        e*finrank K (biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F G) := by
  have he := injective_pi_quotient_finrank (oddEvenRelativeMap Q F G (oddEvenAffineFamily E a)) hi
  exact Nat.eq_sub_of_add_eq he.symm

end Froberg
