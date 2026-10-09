module

public import Froberg.LinearCutVectors
public import Froberg.BiformDegreeTransport
public import Froberg.TensorVectorEmbedding
public import Froberg.StrictVectorModel

@[expose] public section

/-! Explicit linear-output tensor coordinates for actual vector-valued
homogeneous polynomial rows. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial TensorProduct Quartic.ClosedCovectorEquations
open Quartic.BilinearCovectorCharts VectorMultiplicationCoordinates
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m s d : ℕ}

theorem linearCutMap_injective : Function.Injective (linearCutMap (K := K) (n := h)) := by
  classical
  intro x y he
  funext i
  have ht := congrArg (fun p : Forms K h 1 => eval (Pi.single i 1) p.val) he
  change eval (Pi.single i 1) (linearForm x).val=eval (Pi.single i 1) (linearForm y).val at ht
  simpa only [eval_linearForm,covector_apply,Pi.single_apply,ite_mul,one_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true] using ht

def linearCutEquiv : (Fin h → K) ≃ₗ[K] Forms K h 1 :=
  LinearEquiv.ofBijective linearCutMap ⟨linearCutMap_injective,linearCutMap_surjective⟩

@[simp] theorem linearCutEquiv_single (i : Fin h) :
    (linearCutEquiv (Pi.single i (1 : K))).val=X i := by
  classical
  change (linearForm (Pi.single i 1)).val=X i
  simp [linearForm,Pi.single_apply]

def linearOutputTensorEquiv : Rows K h m s ≃ₗ[K] (Forms K h 1 ⊗[K] Forms K m s) :=
  (TensorProduct.piScalarRight K K (Forms K m s) (Fin h)).symm.trans
    ((TensorProduct.comm K (Forms K m s) (Fin h → K)).trans
      (TensorProduct.congr linearCutEquiv (LinearEquiv.refl K (Forms K m s))))

@[simp] theorem linearOutputTensorEquiv_single (i : Fin h) (p : Forms K m s) :
    linearOutputTensorEquiv (Pi.single i p)=linearCutEquiv (Pi.single i (1 : K)) ⊗ₜ[K] p := by
  simp only [linearOutputTensorEquiv,LinearEquiv.trans_apply,TensorProduct.piScalarRight_symm_single,
    TensorProduct.comm_tmul,TensorProduct.congr_tmul,LinearEquiv.refl_apply]

theorem linearOutputTensorEquiv_sum (v : Rows K h m s) :
    linearOutputTensorEquiv v=∑ i,linearCutEquiv (Pi.single i (1 : K)) ⊗ₜ[K] v i := by
  classical
  have he : v=∑ i,Pi.single i (v i) := by ext i; simp
  calc
    linearOutputTensorEquiv v=linearOutputTensorEquiv (∑ i,Pi.single i (v i)) := congrArg _ he
    _=∑ i,linearOutputTensorEquiv (Pi.single i (v i)) := map_sum (linearOutputTensorEquiv (K := K) (h := h) (m := m) (s := s)) (fun i => Pi.single i (v i)) Finset.univ
    _=_ := by simp only [linearOutputTensorEquiv_single]

theorem sumBiformMap_linearOutput (v : Rows K h m s) :
    sumBiformMap (linearOutputTensorEquiv v)=∑ i,rename Sum.inl (X i)*rename Sum.inr (v i).val := by
  rw [linearOutputTensorEquiv_sum,map_sum]
  simp only [sumBiformMap_tmul,linearCutEquiv_single]

theorem linearOutput_scalar_product (p : Forms K m d) (v : Rows K h m s) :
    sumBiformMap (linearOutputTensorEquiv (multiplication p v))=
      rename Sum.inr p.val*sumBiformMap (linearOutputTensorEquiv v) := by
  simp only [sumBiformMap_linearOutput,multiplication_val,map_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Froberg
