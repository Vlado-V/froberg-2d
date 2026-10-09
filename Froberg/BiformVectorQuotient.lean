module

public import Froberg.BiformVectorDetector
public import Mathlib.LinearAlgebra.TensorProduct.Pi

@[expose] public section

/-! Output tensor quotients agree with coordinatewise scalar quotients.
Detected independence therefore removes the product coefficients from
any relation whose remaining scalar coordinates lie in the old space. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K]
variable {σ I : Type*} {n c : ℕ}

def outputTensorVectorEquiv (V : Type*) [AddCommGroup V] [Module K V] :
    (Fin c → K) ⊗[K] V ≃ₗ[K] (Fin c → V) :=
  (TensorProduct.comm K (Fin c → K) V).trans (TensorProduct.piScalarRight K K V (Fin c))

@[simp] theorem outputTensorVectorEquiv_tmul
    {V : Type*} [AddCommGroup V] [Module K V] (a : Fin c → K) (v : V) :
    outputTensorVectorEquiv (K := K) V (a ⊗ₜ[K] v)=fun k => a k • v := by
  simp only [outputTensorVectorEquiv,LinearEquiv.trans_apply,TensorProduct.comm_tmul,
    TensorProduct.piScalarRight_apply,TensorProduct.piScalarRightHom_tmul]

theorem outputTensorVectorEquiv_biform_quotient
    (T : MvPolynomial σ K →ₗ[K] (Fin c → K))
    (Q : Submodule K (Poly K n)) (p : MvPolynomial (σ ⊕ Fin n) K) :
    outputTensorVectorEquiv (Poly K n ⧸ Q)
      (TensorProduct.map (LinearMap.id : (Fin c → K) →ₗ[K] _) Q.mkQ
        (biformOutputMap T p))=
      fun k => Q.mkQ (biformVectorDetector T p k) := by
  obtain ⟨z,rfl⟩ := (tensorEquivSum K σ (Fin n) K).surjective p
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [tensorEquivSum_tmul,biformOutputMap_tmul,TensorProduct.map_tmul,
      LinearMap.id_apply,outputTensorVectorEquiv_tmul,biformVectorDetector_tmul,map_smul]
  | add a b ha hb =>
    funext k
    simpa only [map_add,Pi.add_apply] using congrFun (congrArg₂ HAdd.hAdd ha hb) k

theorem detected_biform_coordinate_quotient_independent
    (T : MvPolynomial σ K →ₗ[K] (Fin c → K))
    (Q : Submodule K (Poly K n)) (p : I → MvPolynomial (σ ⊕ Fin n) K)
    (hp : LinearIndependent K (fun i =>
      TensorProduct.map (LinearMap.id : (Fin c → K) →ₗ[K] _) Q.mkQ (biformOutputMap T (p i)))) :
    LinearIndependent K (fun i k => Q.mkQ (biformVectorDetector T (p i) k)) := by
  let e := outputTensorVectorEquiv (K := K) (c := c) (Poly K n ⧸ Q)
  have hi := hp.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  simpa only [Function.comp_def,LinearEquiv.coe_coe,e,
    outputTensorVectorEquiv_biform_quotient] using hi

theorem detected_biform_vector_relation_coefficients [Fintype I]
    (T : MvPolynomial σ K →ₗ[K] (Fin c → K))
    (Q : Submodule K (Poly K n)) (p : I → MvPolynomial (σ ⊕ Fin n) K)
    (hp : LinearIndependent K (fun i =>
      TensorProduct.map (LinearMap.id : (Fin c → K) →ₗ[K] _) Q.mkQ (biformOutputMap T (p i))))
    (g : Fin c → Poly K n) (hg : ∀ k,g k∈Q) (a : I → K)
    (hrel : g+∑ i,a i • biformVectorDetector T (p i)=0) : a=0 := by
  have hi := detected_biform_coordinate_quotient_independent T Q p hp
  have hz : (∑ i,a i • (fun k => Q.mkQ (biformVectorDetector T (p i) k)))=0 := by
    funext k
    have hh := congrArg (fun v : Fin c → Poly K n => Q.mkQ (v k)) hrel
    have hzero : Q.mkQ (g k)=0 := (Submodule.Quotient.mk_eq_zero Q).mpr (hg k)
    simpa only [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,map_add,map_sum,map_smul,
      hzero,zero_add,Pi.zero_apply,map_zero] using hh
  exact funext (Fintype.linearIndependent_iff.mp hi a hz)

end Froberg
