module

public import Froberg.CoreTensorProjection
public import Froberg.BiformVectorDetector

@[expose] public section

/-! The coordinate detector on the literal single-ring polynomial model.
It is supported in quadratic output degree and kills constrained quadratic
background products and every scalar-only polynomial. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K] {h m c d : ℕ}

/-- Apply the output detector coefficientwise after splitting the variables. -/
def preparedQuadraticDetector (T : Poly K h →ₗ[K] (Fin c → K)) :
    Poly K (h+m) →ₗ[K] (Fin c → Poly K m) :=
  (biformVectorDetector T).comp (rename finSumFinEquiv.symm).toLinearMap

omit [Infinite K] in
@[simp] theorem preparedQuadraticDetector_rename
    (T : Poly K h →ₗ[K] (Fin c → K)) (p : MvPolynomial (Fin h ⊕ Fin m) K) :
    preparedQuadraticDetector T (rename finSumFinEquiv p)=biformVectorDetector T p := by
  change biformVectorDetector T (rename finSumFinEquiv.symm (rename finSumFinEquiv p))=_
  exact congrArg (biformVectorDetector T) ((renameEquiv K finSumFinEquiv).left_inv p)

@[simp] theorem preparedQuadraticDetector_tmul
    (T : Poly K h →ₗ[K] (Fin c → K)) (a : Poly K h) (b : Poly K m) (k : Fin c) :
    preparedQuadraticDetector T (splitPolynomialEquiv (K := K) h m (a ⊗ₜ[K] b)) k=
      T a k • b := by
  change biformVectorDetector T (rename finSumFinEquiv.symm
    (splitPolynomialEquiv (K := K) h m (a ⊗ₜ[K] b))) k=_
  rw [splitPolynomialEquiv_tmul,map_mul,rename_rename,rename_rename]
  have hl : (finSumFinEquiv.symm ∘ Fin.castAdd m : Fin h → Fin h ⊕ Fin m)=Sum.inl :=
    funext fun i => finSumFinEquiv_symm_apply_castAdd i
  have hr : (finSumFinEquiv.symm ∘ Fin.natAdd h : Fin m → Fin h ⊕ Fin m)=Sum.inr :=
    funext fun i => finSumFinEquiv_symm_apply_natAdd i
  rw [hl,hr,biformVectorDetector_tmul]

@[simp] theorem preparedQuadraticDetector_mul_rename
    (T : Poly K h →ₗ[K] (Fin c → K)) (a : Poly K h) (b : Poly K m) (k : Fin c) :
    preparedQuadraticDetector T (rename (Fin.castAdd m) a * rename (Fin.natAdd h) b) k=
      T a k • b := by
  simpa only [splitPolynomialEquiv_tmul] using preparedQuadraticDetector_tmul T a b k

theorem preparedQuadraticDetector_supported
    (T : Poly K h →ₗ[K] (Fin c → K))
    (hT : T.comp (homogeneousComponent 2)=T) :
    (preparedQuadraticDetector (m := m) T).comp (coreComponent h m 2)=
      preparedQuadraticDetector T := by
  apply LinearMap.ext
  intro p
  obtain ⟨v,rfl⟩ := (splitPolynomialEquiv (K := K) h m).surjective p
  induction v using TensorProduct.inductionOn with
  | tmul a b =>
    change preparedQuadraticDetector T
      (coreComponent h m 2 (splitPolynomialEquiv (K := K) h m (a ⊗ₜ[K] b)))=_
    rw [coreComponent_split_tmul]
    funext k
    rw [preparedQuadraticDetector_tmul,preparedQuadraticDetector_tmul]
    have he := LinearMap.congr_fun hT a
    change T (homogeneousComponent 2 a)=T a at he
    rw [he]
  | add a b ha hb =>
    simpa only [map_add,LinearMap.comp_apply] using congrArg₂ HAdd.hAdd ha hb

omit [Infinite K] in
/-- A detector supported in degree two vanishes on the constant polynomial. -/
theorem quadratic_output_one_zero (T : Poly K h →ₗ[K] (Fin c → K))
    (hT : T.comp (homogeneousComponent 2)=T) : T 1=0 := by
  have he := LinearMap.congr_fun hT (1 : Poly K h)
  change T (homogeneousComponent 2 1)=T 1 at he
  rw [homogeneousComponent_of_mem (isHomogeneous_one _ _)] at he
  simpa using he.symm

/-- Every polynomial supported only in the scalar variables is invisible. -/
theorem preparedQuadraticDetector_scalar
    (T : Poly K h →ₗ[K] (Fin c → K))
    (hT : T.comp (homogeneousComponent 2)=T) (p : Poly K m) :
    preparedQuadraticDetector T (rename (Fin.natAdd h) p)=0 := by
  have hp : rename (Fin.natAdd h) p=
      splitPolynomialEquiv (K := K) h m ((1 : Poly K h) ⊗ₜ[K] p) := by
    rw [splitPolynomialEquiv_tmul,map_one,one_mul]
  rw [hp]
  funext k
  rw [preparedQuadraticDetector_tmul,quadratic_output_one_zero T hT]
  simp

/-- A killed output subspace remains killed with arbitrary scalar coefficients. -/
theorem polynomialTensorSpace_le_preparedQuadraticDetector_ker
    (T : Poly K h →ₗ[K] (Fin c → K))
    (A : Submodule K (Poly K h)) (B : Submodule K (Poly K m)) (hA : A≤T.ker) :
    polynomialTensorSpace A B≤(preparedQuadraticDetector T).ker := by
  rintro p ⟨z,rfl⟩
  change preparedQuadraticDetector T (polynomialTensorMap A B z)=0
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    funext k
    rw [polynomialTensorMap_tmul,preparedQuadraticDetector_tmul]
    have hz : T a.val=0 := hA a.property
    rw [hz]
    simp
  | add a b ha hb => simp only [map_add,ha,hb,add_zero]

/-- Products are killed whenever their output-factor product is killed. -/
theorem polynomialTensorSpace_product_le_preparedQuadraticDetector_ker
    (T : Poly K h →ₗ[K] (Fin c → K))
    (A C : Submodule K (Poly K h)) (B E : Submodule K (Poly K m))
    (hAC : A*C≤T.ker) :
    polynomialTensorSpace A B * polynomialTensorSpace C E≤
      (preparedQuadraticDetector T).ker := by
  apply Submodule.mul_le.mpr
  rintro p ⟨z,rfl⟩ q ⟨w,rfl⟩
  change preparedQuadraticDetector T
    (polynomialTensorMap A B z * polynomialTensorMap C E w)=0
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    induction w using TensorProduct.inductionOn with
    | tmul x y =>
      funext k
      rw [polynomialTensorMap_tmul,polynomialTensorMap_tmul,←map_mul,
        Algebra.TensorProduct.tmul_mul_tmul,preparedQuadraticDetector_tmul]
      have hz : T (a.val*x.val)=0 := hAC (Submodule.mul_mem_mul a.property x.property)
      rw [hz]
      simp
    | add x y hx hy => simp only [map_add,mul_add,hx,hy,add_zero]
  | add x y hx hy => simp only [map_add,add_mul,hx,hy,add_zero]

/-- The constrained quadratic term stays invisible after multiplying by any
scalar-only coefficient of the required total degree. -/
theorem preparedQuadraticDetector_quadratic_product
    (T : Poly K h →ₗ[K] (Fin c → K)) (D : Submodule K (Poly K h))
    (hD : D≤T.ker) :
    polynomialTensorSpace D (Forms K m (d-2)) * coreCoefficientSpace K h m d 0≤
      (preparedQuadraticDetector T).ker := by
  have hc : coreCoefficientSpace K h m d 0=
      polynomialTensorSpace (Forms K h 0) (Forms K m d) := by
    simpa only [zero_add] using
      (coreCoefficientSpace_eq_polynomialTensorSpace (K := K) (h := h) (m := m) 0 d)
  rw [hc]
  apply polynomialTensorSpace_product_le_preparedQuadraticDetector_ker
  simpa only [Forms,homogeneousSubmodule_zero,mul_one] using hD

end Froberg
