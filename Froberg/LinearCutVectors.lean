module

public import Froberg.ClosedKernelSlices

@[expose] public section

/-! Every homogeneous linear covector cut is the annihilator of an actual
target vector, including a zero-dimensional target. -/
noncomputable section
namespace Froberg
open MvPolynomial Quartic ClosedCovectorEquations
variable {K : Type*} [Field K] {n : ℕ}

def linearCutMap : (Fin n → K) →ₗ[K] Forms K n 1 where
  toFun := linearForm
  map_add' x y := by
    apply Subtype.ext
    simp [linearForm,map_add,add_mul,Finset.sum_add_distrib]
  map_smul' a x := by
    apply Subtype.ext
    simp [linearForm,smul_eq_C_mul,Finset.mul_sum,mul_assoc]

theorem linearCutMap_surjective : Function.Surjective (linearCutMap (K := K) (n := n)) := by
  classical
  let L := (Forms K n 1).subtype.comp (linearCutMap (K := K) (n := n))
  have hspan : Forms K n 1 ≤ L.range := by
    rw [Forms,homogeneousSubmodule_one_eq_span_X]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    refine ⟨Pi.single i 1,?_⟩
    simp [L,linearCutMap,linearForm,Pi.single_apply]
  intro f
  obtain ⟨v,hv⟩ := hspan f.property
  exact ⟨v,Subtype.ext hv⟩

theorem exists_linearCutVector (f : Forms K n 1) : ∃ v : Fin n → K,linearForm v=f :=
  linearCutMap_surjective f

end Froberg
