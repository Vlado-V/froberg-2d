import Froberg.BiformScalarProjection
import Froberg.BiformOutputConstraint

/-! Output coordinate projections preserve scalar coefficient spaces. -/
noncomputable section
namespace Froberg
open MvPolynomial TensorProduct
open scoped Classical
variable {K : Type} [Field K] {σ τ : Type*}

def biformOutputEndomorphism (T : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) :
    MvPolynomial (σ ⊕ τ) K →ₗ[K] MvPolynomial (σ ⊕ τ) K :=
  (MvPolynomial.tensorEquivSum K σ τ K).toLinearMap.comp
    ((TensorProduct.map T LinearMap.id).comp
      (MvPolynomial.tensorEquivSum K σ τ K).symm.toLinearMap)

@[simp] theorem biformOutputEndomorphism_tmul
    (T : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (a : MvPolynomial σ K) (b : MvPolynomial τ K) :
    biformOutputEndomorphism T (rename Sum.inl a * rename Sum.inr b) =
      rename Sum.inl (T a) * rename Sum.inr b := by
  rw [← tensorEquivSum_tmul]
  simp only [biformOutputEndomorphism,LinearMap.comp_apply,AlgEquiv.toLinearMap_apply,
    AlgEquiv.symm_apply_apply,TensorProduct.map_tmul,LinearMap.id_apply]
  exact tensorEquivSum_tmul (T a) b

def outputExponent (a : (σ ⊕ τ) →₀ ℕ) : σ →₀ ℕ :=
  a.comapDomain Sum.inl Sum.inl_injective.injOn

theorem biformOutputEndomorphism_retain (P : (σ →₀ ℕ) → Prop) :
    biformOutputEndomorphism (K := K) (τ := τ) (retainMonomials P) =
      retainMonomials (fun a => P (outputExponent a)) := by
  apply LinearMap.ext
  intro f
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial a c =>
    obtain ⟨⟨u,v⟩,rfl⟩ := (Finsupp.sumFinsuppEquivProdFinsupp (α := σ) (β := τ) (γ := ℕ)).symm.surjective a
    change biformOutputEndomorphism (retainMonomials P) (monomial (u.sumElim v) c) =
      retainMonomials (fun a => P (outputExponent a)) (monomial (u.sumElim v) c)
    rw [retainMonomials_monomial]
    simp only [outputExponent,Finsupp.comapDomain_inl_sumElim]
    rw [monomial_sumElim,biformOutputEndomorphism_tmul,retainMonomials_monomial]
    split_ifs <;> simp

@[simp] theorem outputExponent_weight [Fintype σ] [Fintype τ]
    (w : σ → ℕ) (a : (σ ⊕ τ) →₀ ℕ) :
    Finsupp.weight w (outputExponent a) =
      Finsupp.weight (Sum.elim w (fun _ : τ => 0)) a := by
  simp [Finsupp.weight_eq_sum,Fintype.sum_sum_type,outputExponent]

theorem biformOutputEndomorphism_preserves [Infinite K]
    (O : Submodule K (MvPolynomial σ K)) (C : Submodule K (MvPolynomial τ K))
    (T : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (hT : ∀ f∈O,T f∈O) {f : MvPolynomial (σ ⊕ τ) K} (hf : f∈biformImage O C) :
    biformOutputEndomorphism T f∈biformImage O C := by
  rcases hf with ⟨a,⟨z,rfl⟩,rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    change biformOutputEndomorphism T
      (MvPolynomial.tensorEquivSum K σ τ K (a.val ⊗ₜ[K] b.val))∈_
    rw [tensorEquivSum_tmul,biformOutputEndomorphism_tmul]
    exact mul_mem_biformImage O C (hT a.val a.property) b.property
  | add a b ha hb => simpa only [map_add] using (biformImage O C).add_mem ha hb

theorem retainMonomials_preserves_homogeneous
    (P : (σ →₀ ℕ) → Prop) {f : MvPolynomial σ K} {R : ℕ}
    (hf : f.IsHomogeneous R) : (retainMonomials P f).IsHomogeneous R := by
  intro a ha
  rw [coeff_retainMonomials] at ha
  split_ifs at ha with hP
  · exact hf ha
  · exact False.elim (ha rfl)

/-- A half-degree projection acts as identity on its retained homogeneous
profile, and as zero on every deleted profile. -/
theorem retainMonomials_weighted (w : σ → ℕ) (P : ℕ → Prop)
    {f : MvPolynomial σ K} {r : ℕ} (hf : f.IsWeightedHomogeneous w r) :
    retainMonomials (fun a => P (Finsupp.weight w a)) f = if P r then f else 0 := by
  ext a
  rw [coeff_retainMonomials]
  by_cases ha : f.coeff a=0
  · split_ifs <;> simp [ha]
  · have hw := hf ha
    simp only [hw]
    split_ifs <;> rfl

end Froberg
