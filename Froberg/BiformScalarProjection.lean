module

public import Froberg.BiformWitnesses
public import Froberg.RetainedMonomials
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

/-! Scalar coordinate projection on a biform is the genuine tensor extension
of the scalar projection. Thus scalar injectivity remains valid with arbitrary
output coefficients. -/
noncomputable section
namespace Froberg
open MvPolynomial TensorProduct
open scoped Classical
variable {K : Type} [Field K] {σ τ : Type*}

/-- Apply a scalar-space linear map coefficientwise in the output variables. -/
def biformScalarMap (L : MvPolynomial τ K →ₗ[K] MvPolynomial τ K) :
    MvPolynomial (σ ⊕ τ) K →ₗ[K] MvPolynomial (σ ⊕ τ) K :=
  (MvPolynomial.tensorEquivSum K σ τ K).toLinearMap.comp
    ((TensorProduct.map LinearMap.id L).comp
      (MvPolynomial.tensorEquivSum K σ τ K).symm.toLinearMap)

@[simp] theorem biformScalarMap_tmul (L : MvPolynomial τ K →ₗ[K] MvPolynomial τ K)
    (a : MvPolynomial σ K) (b : MvPolynomial τ K) :
    biformScalarMap L (rename Sum.inl a * rename Sum.inr b) =
      rename Sum.inl a * rename Sum.inr (L b) := by
  rw [← tensorEquivSum_tmul]
  simp only [biformScalarMap,LinearMap.comp_apply,AlgEquiv.toLinearMap_apply,
    AlgEquiv.symm_apply_apply,TensorProduct.map_tmul,LinearMap.id_apply]
  exact tensorEquivSum_tmul a (L b)

theorem monomial_sumElim (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c : K) :
    (monomial (a.sumElim b) c : MvPolynomial (σ ⊕ τ) K) =
      rename Sum.inl (monomial a c) * rename Sum.inr (monomial b 1) := by
  rw [rename_monomial,rename_monomial,monomial_mul, mul_one,Finsupp.sumElim_eq_add]

theorem retainMonomials_monomial (P : (τ →₀ ℕ) → Prop) (a : τ →₀ ℕ) (c : K) :
    retainMonomials P (monomial a c) = if P a then monomial a c else 0 := by
  classical
  by_cases hP : P a
  · rw [if_pos hP]
    ext b
    by_cases hab : a=b
    · subst b; simp [coeff_retainMonomials,hP]
    · simp [coeff_retainMonomials,coeff_monomial,hab]
  · rw [if_neg hP]
    ext b
    by_cases hab : a=b
    · subst b; simp [coeff_retainMonomials,hP]
    · simp [coeff_retainMonomials,coeff_monomial,hab]

/-- The scalar exponent of a monomial in the sum of the variable sets. -/
def scalarExponent (a : (σ ⊕ τ) →₀ ℕ) : τ →₀ ℕ :=
  a.comapDomain Sum.inr Sum.inr_injective.injOn

/-- Tensor projection and coordinate projection agree exactly. -/
theorem biformScalarMap_retain (P : (τ →₀ ℕ) → Prop) :
    biformScalarMap (K := K) (σ := σ) (retainMonomials P) =
      retainMonomials (fun a => P (scalarExponent a)) := by
  classical
  apply LinearMap.ext
  intro f
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial a c =>
    obtain ⟨⟨u,v⟩,rfl⟩ := (Finsupp.sumFinsuppEquivProdFinsupp (α := σ) (β := τ) (γ := ℕ)).symm.surjective a
    change biformScalarMap (retainMonomials P) (monomial (u.sumElim v) c) =
      retainMonomials (fun a => P (scalarExponent a)) (monomial (u.sumElim v) c)
    rw [retainMonomials_monomial]
    simp only [scalarExponent,Finsupp.comapDomain_inr_sumElim]
    rw [monomial_sumElim,biformScalarMap_tmul,retainMonomials_monomial]
    split_ifs <;> simp

/-- If scalar projection is injective on the scalar coefficient space, its
tensor extension is injective on the full biform space. -/
theorem biformImage_disjoint_scalar_kernel [Infinite K]
    (O : Submodule K (MvPolynomial σ K)) (C : Submodule K (MvPolynomial τ K))
    (L : MvPolynomial τ K →ₗ[K] MvPolynomial τ K) (hC : Disjoint C L.ker) :
    Disjoint (biformImage O C) (biformScalarMap (σ := σ) L).ker := by
  have hLC : Function.Injective (L.comp C.subtype) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply Subtype.ext
    exact (Submodule.disjoint_def.mp hC) x.val x.property hx
  have ht : Function.Injective (TensorProduct.map O.subtype (L.comp C.subtype)) :=
    TensorProduct.map_injective_of_flat_flat _ _ O.subtype_injective hLC
  apply Submodule.disjoint_def.mpr
  rintro f ⟨g,⟨z,rfl⟩,rfl⟩ hf
  have hz : TensorProduct.map O.subtype (L.comp C.subtype) z=0 := by
    change biformScalarMap L (MvPolynomial.tensorEquivSum K σ τ K
      (TensorProduct.map O.subtype C.subtype z))=0 at hf
    unfold biformScalarMap at hf
    simp only [LinearMap.comp_apply,AlgEquiv.toLinearMap_apply,AlgEquiv.symm_apply_apply] at hf
    have hzero := (MvPolynomial.tensorEquivSum K σ τ K).injective (hf.trans (map_zero _).symm)
    rw [← LinearMap.comp_apply,← TensorProduct.map_comp] at hzero
    simpa only [LinearMap.id_comp] using hzero
  have hz0 : z=0 := ht (hz.trans (map_zero _).symm)
  simp [hz0]

end Froberg
