import Froberg.BottomVectorRows
import Froberg.ScalarLayerQuotientExact
import Froberg.EvenCoefficientElimination

/-! The actual first odd polynomial row has precisely the scalar–vector
constant relations whenever scalar multiplication on the vector quotient
is injective. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg
open Module MvPolynomial TensorProduct Quartic VectorMultiplicationCoordinates
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}

theorem bottom_polynomial_constants (hd : 1≤d)
    (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1))
    (hg : Function.Injective (BilinearImage.tupleMap (multiplication (d := d)) g))
    (hQ : Function.Injective (BilinearScalarFamily.multiplication
      (VectorExpansionOpen.quotientMultiplication g d) Q))
    (u : Fin q → MvPolynomial (Fin h ⊕ Fin m) K)
    (v : Fin f → MvPolynomial (Fin h ⊕ Fin m) K)
    (hu : ∀ i,u i∈coefficientComponentSpace (Sum.elim (fun _ => 1) (fun _ => 0)) d 1)
    (hv : ∀ i,v i∈coefficientComponentSpace (Sum.elim (fun _ => 1) (fun _ => 0)) d 0)
    (hrow : (∑ i,rename Sum.inr (Q i).val*u i)+
      (∑ j,sumBiformMap (linearOutputTensorEquiv (g j))*v j)=0) :
    ∃ C : Fin q → Fin f → K,
      (∀ i,u i=∑ j,C i j • sumBiformMap (linearOutputTensorEquiv (g j))) ∧
      ∀ j,v j = -∑ i,C i j • rename Sum.inr (Q i).val := by
  classical
  have hu' (i) : ∃ x : Rows K h m (d-1),sumBiformMap (linearOutputTensorEquiv x)=u i := by
    obtain ⟨z,hz⟩ := exists_sumBiformMap_of_homogeneous (a := 1) (c := d-1)
      (by simpa only [show 1+(d-1)=d by omega] using (show (u i).IsHomogeneous d from (hu i).1)) (hu i).2
    exact ⟨linearOutputTensorEquiv.symm z,by simpa using hz⟩
  have hv' (j) : ∃ y : Forms K m d,rename Sum.inr y.val=v j := by
    obtain ⟨z,hz⟩ := exists_sumBiformMap_of_homogeneous (a := 0) (c := d)
      (by simpa only [zero_add] using (show (v j).IsHomogeneous d from (hv j).1)) (hv j).2
    refine ⟨scalarBiformEquiv.symm z,?_⟩
    rw [←sumBiformMap_scalarBiform,LinearEquiv.apply_symm_apply]
    exact hz
  choose x hx using hu'
  choose y hy using hv'
  have hr : (∑ i,multiplication (Q i) (x i))+(∑ j,multiplication (y j) (g j))=0 := by
    apply (sumBiformMap_injective.comp linearOutputTensorEquiv.injective)
    simp only [Function.comp_apply,map_add,map_sum,map_zero,linearOutput_scalar_product,hx,hy]
    simpa only [mul_comm] using hrow
  obtain ⟨C,hC,hC'⟩ := scalar_layer_constants_of_quotient_injective multiplication Q g hg hQ x y hr
  refine ⟨C,?_,?_⟩
  · intro i
    rw [←hx i,hC i]
    simp only [map_sum,map_smul]
  · intro j
    rw [←hy j,hC' j]
    simp only [Submodule.coe_neg,Submodule.coe_sum,Submodule.coe_smul,map_neg,map_sum,map_smul]

end Froberg
