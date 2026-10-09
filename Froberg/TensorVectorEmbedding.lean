module

public import Froberg.BiformWitnesses
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

@[expose] public section

/-! Faithful transport from vector-valued polynomial rows to actual
polynomials with independent output forms. -/
noncomputable section
namespace Froberg
open TensorProduct MvPolynomial
variable {K : Type} [Field K]
variable {A V : Type*} [AddCommGroup A] [Module K A] [AddCommGroup V] [Module K V]
variable {I : Type*} [Fintype I]

def tensorVector (o : I → A) : (I → V) →ₗ[K] A ⊗[K] V where
  toFun p := ∑ i, o i ⊗ₜ[K] p i
  map_add' p q := by simp [tmul_add,Finset.sum_add_distrib]
  map_smul' c p := by simp [tmul_smul,Finset.smul_sum]

theorem tensorVector_injective (o : I → A) (ho : LinearIndependent K o) :
    Function.Injective (tensorVector (K := K) (V := V) o) := by
  classical
  obtain ⟨L,hL⟩ := (Finsupp.linearCombination K o).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr ho)
  have hLo (i : I) : L (o i)=Finsupp.single i 1 := by
    have hh := LinearMap.congr_fun hL (Finsupp.single i 1)
    simpa only [LinearMap.comp_apply,Finsupp.linearCombination_single,one_smul,
      LinearMap.id_apply] using hh
  let T (i : I) : A ⊗[K] V →ₗ[K] V :=
    (TensorProduct.lid K V).toLinearMap.comp
      (TensorProduct.map ((Finsupp.lapply i).comp L) LinearMap.id)
  have hT (i : I) (p : I → V) : T i (tensorVector o p)=p i := by
    simp only [T,tensorVector,LinearMap.coe_mk,AddHom.coe_mk,map_sum,LinearMap.comp_apply,
      TensorProduct.map_tmul,LinearMap.id_apply,Finsupp.lapply_apply,hLo,
      LinearEquiv.coe_coe,TensorProduct.lid_tmul,Finsupp.single_apply]
    simp
  intro p q hpq
  funext i
  have hh := congrArg (T i) hpq
  simpa only [hT] using hh

variable {σ τ : Type*}

def polynomialVector (o : I → MvPolynomial σ K) :
    (I → MvPolynomial τ K) →ₗ[K] MvPolynomial (σ ⊕ τ) K :=
  (MvPolynomial.tensorEquivSum K σ τ K).toLinearMap.comp (tensorVector o)

theorem polynomialVector_apply (o : I → MvPolynomial σ K) (p : I → MvPolynomial τ K) :
    polynomialVector o p = ∑ i, rename Sum.inl (o i) * rename Sum.inr (p i) := by
  simp only [polynomialVector,LinearMap.comp_apply,tensorVector,LinearMap.coe_mk,AddHom.coe_mk,
    map_sum,AlgEquiv.toLinearMap_apply,tensorEquivSum_tmul]

theorem polynomialVector_injective (o : I → MvPolynomial σ K) (ho : LinearIndependent K o) :
    Function.Injective (polynomialVector (τ := τ) o) :=
  (MvPolynomial.tensorEquivSum K σ τ K).injective.comp (tensorVector_injective o ho)

theorem polynomialVector_homogeneous (o : I → MvPolynomial σ K) (p : I → MvPolynomial τ K)
    {R s : ℕ} (ho : ∀ i, (o i).IsHomogeneous R) (hp : ∀ i, (p i).IsHomogeneous s) :
    (polynomialVector o p).IsHomogeneous (R+s) := by
  rw [polynomialVector_apply]
  apply IsHomogeneous.sum
  intro i hi
  exact (ho i).rename_isHomogeneous.mul (hp i).rename_isHomogeneous

theorem polynomialVector_scalar_mul (o : I → MvPolynomial σ K)
    (p : I → MvPolynomial τ K) (f : MvPolynomial τ K) :
    polynomialVector o (fun i => f*p i) = rename Sum.inr f * polynomialVector o p := by
  simp only [polynomialVector_apply,map_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end Froberg
