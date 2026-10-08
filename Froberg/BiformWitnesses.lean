import Froberg.FourBlockVariables
import Froberg.CrossCoefficientSpaces
import Froberg.PairedDiagonalSpace
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! Actual four-block polynomial witnesses for individual cross and
diagonal factors in the product row. -/
noncomputable section
set_option maxHeartbeats 800000
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K]
variable {σ τ : Type*}

def biformImage (O : Submodule K (MvPolynomial σ K))
    (C : Submodule K (MvPolynomial τ K)) : Submodule K (MvPolynomial (σ ⊕ τ) K) :=
  (LinearMap.range (TensorProduct.map O.subtype C.subtype)).map
    (MvPolynomial.tensorEquivSum K σ τ K).toLinearMap

/-- Full finite tensor capacity in the sum-variable polynomial model. -/
theorem exists_independent_sum_biforms (O : Submodule K (MvPolynomial σ K))
    (C : Submodule K (MvPolynomial τ K)) [Module.Finite K O] [Module.Finite K C]
    {m : ℕ} (hm : m ≤ finrank K O * finrank K C) :
    ∃ q : Fin m → MvPolynomial (σ ⊕ τ) K,
      (∀ i, q i ∈ biformImage O C) ∧ LinearIndependent K q := by
  obtain ⟨a,ha,hi⟩ := exists_independent_tensor_family O C hm
  let e := MvPolynomial.tensorEquivSum K σ τ K
  refine ⟨fun i => e (a i),fun i => ⟨a i,ha i,rfl⟩,?_⟩
  exact hi.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)

/-- Homogeneous biforms have the sum of their two total degrees. -/
theorem biformImage_homogeneous (O : Submodule K (MvPolynomial σ K))
    (C : Submodule K (MvPolynomial τ K)) {j t : ℕ}
    (hO : O ≤ homogeneousSubmodule σ K j) (hC : C ≤ homogeneousSubmodule τ K t) :
    biformImage O C ≤ homogeneousSubmodule (σ ⊕ τ) K (j+t) := by
  rintro p ⟨a,⟨z,rfl⟩,rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    change (MvPolynomial.tensorEquivSum K σ τ K (a.val ⊗ₜ[K] b.val)).IsHomogeneous (j+t)
    rw [tensorEquivSum_tmul]
    exact (hO a.property).rename_isHomogeneous.mul (hC b.property).rename_isHomogeneous
  | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb

/-- Scalar weight, complementary to output weight, in a sum of variables. -/
theorem biformImage_scalar_weight (O : Submodule K (MvPolynomial σ K))
    (C : Submodule K (MvPolynomial τ K)) {t : ℕ}
    (hC : C ≤ homogeneousSubmodule τ K t) :
    biformImage O C ≤ weightedHomogeneousSubmodule K (FourBlocks.scalarWeight (A := σ) (B := τ)) t := by
  rintro p ⟨a,⟨z,rfl⟩,rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    change (MvPolynomial.tensorEquivSum K σ τ K (a.val ⊗ₜ[K] b.val)).IsWeightedHomogeneous _ t
    rw [tensorEquivSum_tmul]
    have hl := rename_weightedHomogeneous (K := K)
      (⟨Sum.inl,Sum.inl_injective⟩ : σ ↪ σ ⊕ τ)
      (fun _ => 0) FourBlocks.scalarWeight (fun _ => rfl) (weightedHomogeneous_zero_weight a.val)
    have hr := rename_weightedHomogeneous (K := K)
      (⟨Sum.inr,Sum.inr_injective⟩ : τ ↪ σ ⊕ τ)
      (fun _ => 1) FourBlocks.scalarWeight (fun _ => rfl) (hC b.property)
    change (rename Sum.inl a.val).IsWeightedHomogeneous FourBlocks.scalarWeight 0 at hl
    change (rename Sum.inr b.val).IsWeightedHomogeneous FourBlocks.scalarWeight t at hr
    simpa only [zero_add] using hl.mul hr
  | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb

/-- Output degree of every biform, independently of scalar coefficients. -/
theorem biformImage_output_weight (O : Submodule K (MvPolynomial σ K))
    (C : Submodule K (MvPolynomial τ K)) {j : ℕ}
    (hO : O ≤ homogeneousSubmodule σ K j) :
    biformImage O C ≤ weightedHomogeneousSubmodule K (FourBlocks.outputWeight (A := σ) (B := τ)) j :=
  tensorImage_weighted (fun _ => 1) O C hO

/-- A finite cross-pair witness, with exact output and scalar half-degrees
and genuinely independent products in one common four-block variable set. -/
theorem exists_fourBlock_cross_pair
    (O₁ O₂ : Submodule K (MvPolynomial σ K))
    (C₁ C₂ : Submodule K (MvPolynomial τ K))
    [Module.Finite K O₁] [Module.Finite K O₂] [Module.Finite K C₁] [Module.Finite K C₂]
    {j l s t a b : ℕ}
    (hO₁ : O₁ ≤ homogeneousSubmodule σ K j) (hO₂ : O₂ ≤ homogeneousSubmodule σ K l)
    (hC₁ : C₁ ≤ homogeneousSubmodule τ K s) (hC₂ : C₂ ≤ homogeneousSubmodule τ K t)
    (ha : a ≤ finrank K O₁ * finrank K C₁) (hb : b ≤ finrank K O₂ * finrank K C₂) :
    ∃ (f : Fin a → MvPolynomial (FourBlocks.Variables σ τ) K)
      (g : Fin b → MvPolynomial (FourBlocks.Variables σ τ) K),
      (∀ i, (f i).IsHomogeneous (j+s) ∧
        (f i).IsWeightedHomogeneous FourBlocks.xHalfWeight j ∧
        (f i).IsWeightedHomogeneous FourBlocks.yHalfWeight s) ∧
      (∀ i, (g i).IsHomogeneous (l+t) ∧
        (g i).IsWeightedHomogeneous FourBlocks.xHalfWeight 0 ∧
        (g i).IsWeightedHomogeneous FourBlocks.yHalfWeight 0) ∧
      LinearIndependent K (fun p : Fin a × Fin b => f p.1 * g p.2) ∧
      (∀ i, f i ∈ (biformImage O₁ C₁).map (rename FourBlocks.leftVar).toLinearMap) ∧
      (∀ i, g i ∈ (biformImage O₂ C₂).map (rename FourBlocks.rightVar).toLinearMap) := by
  obtain ⟨f,hf,hfi⟩ := exists_independent_sum_biforms O₁ C₁ ha
  obtain ⟨g,hg,hgi⟩ := exists_independent_sum_biforms O₂ C₂ hb
  refine ⟨fun i => rename FourBlocks.leftVar (f i),
    fun i => rename FourBlocks.rightVar (g i),?_,?_,FourBlocks.cross_products_independent f g hfi hgi,
      (fun i => ⟨f i,hf i,rfl⟩),(fun i => ⟨g i,hg i,rfl⟩)⟩
  · intro i
    exact ⟨(biformImage_homogeneous O₁ C₁ hO₁ hC₁ (hf i)).rename_isHomogeneous,
      FourBlocks.leftVar_weighted_output (biformImage_output_weight O₁ C₁ hO₁ (hf i)),
      FourBlocks.leftVar_weighted_scalar (biformImage_scalar_weight O₁ C₁ hC₁ (hf i))⟩
  · intro i
    exact ⟨(biformImage_homogeneous O₂ C₂ hO₂ hC₂ (hg i)).rename_isHomogeneous,
      FourBlocks.rightVar_weighted_output (g i),FourBlocks.rightVar_weighted_scalar (g i)⟩

/-- Project a pair-valued weight grading to its first coordinate. -/
theorem weightedHomogeneous_fst {υ : Type*} [Fintype υ]
    (w : υ → ℕ × ℕ) {p : MvPolynomial υ K} {a b : ℕ}
    (hp : p.IsWeightedHomogeneous w (a,b)) :
    p.IsWeightedHomogeneous (fun i => (w i).1) a := by
  intro α hα
  have he : Finsupp.weight (fun i => (w i).1) α = (Finsupp.weight w α).1 := by
    change _ = (AddMonoidHom.fst ℕ ℕ) (Finsupp.weight w α)
    rw [Finsupp.weight_eq_sum,Finsupp.weight_eq_sum,map_sum]
    simp
  rw [he,hp hα]

/-- Arbitrary scalar weight is preserved by the second tensor factor. -/
theorem biformImage_right_weight (w : τ → ℕ)
    (O : Submodule K (MvPolynomial σ K)) (C : Submodule K (MvPolynomial τ K))
    {t : ℕ} (hC : C ≤ weightedHomogeneousSubmodule K w t) :
    biformImage O C ≤ weightedHomogeneousSubmodule K (Sum.elim (fun _ => 0) w) t := by
  rintro p ⟨a,⟨z,rfl⟩,rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    change (MvPolynomial.tensorEquivSum K σ τ K (a.val ⊗ₜ[K] b.val)).IsWeightedHomogeneous _ t
    rw [tensorEquivSum_tmul]
    have hl := rename_weightedHomogeneous (K := K)
      (⟨Sum.inl,Sum.inl_injective⟩ : σ ↪ σ ⊕ τ)
      (fun _ => 0) (Sum.elim (fun _ => 0) w) (fun _ => rfl) (weightedHomogeneous_zero_weight a.val)
    have hr := rename_weightedHomogeneous (K := K)
      (⟨Sum.inr,Sum.inr_injective⟩ : τ ↪ σ ⊕ τ)
      w (Sum.elim (fun _ => 0) w) (fun _ => rfl) (hC b.property)
    change (rename Sum.inl a.val).IsWeightedHomogeneous (Sum.elim (fun _ => 0) w) 0 at hl
    change (rename Sum.inr b.val).IsWeightedHomogeneous (Sum.elim (fun _ => 0) w) t at hr
    simpa only [zero_add] using hl.mul hr
  | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb

/-- A diagonal-pair witness at the exact paired capacity, in the common
four-block polynomial ring and with both half-degrees explicitly recorded. -/
theorem exists_fourBlock_diagonal_pair (w v j t m : ℕ)
    {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]
    (T : MvPolynomial (Fin w × Bool) K →ₗ[K] X)
    (hm : m ≤ (w.choose j - finrank K X) * (v.choose t / 2)) :
    ∃ f : Fin m → MvPolynomial (FourBlocks.Variables (Fin w) (Fin v)) K,
      (∀ i, (f i).IsHomogeneous (j+t) ∧
        (f i).IsWeightedHomogeneous FourBlocks.xHalfWeight (j/2) ∧
        (f i).IsWeightedHomogeneous FourBlocks.yHalfWeight (t/2)) ∧
      LinearIndependent K (pairProducts f) ∧
      (∀ i, TensorProduct.map T (LinearMap.id : MvPolynomial (Fin v × Bool) K →ₗ[K] _)
        ((MvPolynomial.tensorEquivSum K (Fin w × Bool) (Fin v × Bool) K).symm (f i)) = 0) ∧
      ∀ i, (f i).IsWeightedHomogeneous (FourBlocks.outputWeight (A := Fin w × Bool) (B := Fin v × Bool)) j := by
  classical
  obtain ⟨O,C,E,hOh,hOb,hOT,hCh,hCb,hE,hEd,hEi⟩ :=
    paired_diagonal_space_exists (K := K) w v j t m T hm
  letI : Module.Finite K (homogeneousSubmodule (Fin w × Bool) K j) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg _ _ _)
  letI : Module.Finite K (homogeneousSubmodule (Fin v × Bool) K t) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg _ _ _)
  letI : Module.Finite K O := Submodule.finiteDimensional_of_le hOh
  letI : Module.Finite K C := Submodule.finiteDimensional_of_le hCh
  letI : Module.Finite K E := Submodule.finiteDimensional_of_le hE
  subst m
  letI : AddCommGroup E := Module.addCommMonoidToAddCommGroup K
  let b := Module.finBasis K E
  let e := MvPolynomial.tensorEquivSum K (Fin w × Bool) (Fin v × Bool) K
  let f := fun i : Fin (finrank K E) => e (b i).val
  have hf (i) : f i ∈ biformImage O C := ⟨(b i).val,hE (b i).property,rfl⟩
  refine ⟨f,?_,?_,?_,?_⟩
  · intro i
    refine ⟨biformImage_homogeneous O C hOh hCh (hf i),?_,?_⟩
    · have ho' : O ≤ weightedHomogeneousSubmodule K
          (fun z => (PairedMonomials.pairedWeight z).1) (j/2) :=
        fun p hp => weightedHomogeneous_fst PairedMonomials.pairedWeight (hOb hp)
      have hh := tensorImage_weighted _ O C ho' (hf i)
      have hw : FourBlocks.xHalfWeight (A := Fin w) (B := Fin v) =
          leftTensorWeight (fun z : Fin w × Bool => (PairedMonomials.pairedWeight z).1) := by
        funext z
        rcases z with ⟨x,b⟩|⟨y,b⟩ <;> cases b <;> rfl
      rw [hw]
      exact hh
    · have hc' : C ≤ weightedHomogeneousSubmodule K
          (fun z => (PairedMonomials.pairedWeight z).1) (t/2) :=
        fun p hp => weightedHomogeneous_fst PairedMonomials.pairedWeight (hCb hp)
      have hh := biformImage_right_weight _ O C hc' (hf i)
      have hw : FourBlocks.yHalfWeight (A := Fin w) (B := Fin v) =
          Sum.elim (fun _ : Fin w × Bool => 0)
            (fun z : Fin v × Bool => (PairedMonomials.pairedWeight z).1) := by
        funext z
        rcases z with ⟨x,b⟩|⟨y,b⟩ <;> cases b <;> rfl
      rw [hw]
      exact hh
  · have hp := (linearIndependent_pairProducts_in_subspace E hEi b b.linearIndependent).map'
      e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
    convert hp using 1
    funext p
    induction p using Sym2.inductionOn with
    | _ i k => simp only [pairProducts_mk,Function.comp_apply,AlgEquiv.toLinearMap_apply,f,map_mul]
  · intro i
    change TensorProduct.map T LinearMap.id (e.symm (e (b i).val)) = 0
    rw [e.symm_apply_apply]
    obtain ⟨z,hz⟩ := hE (b i).property
    rw [← hz]
    clear hz
    induction z using TensorProduct.inductionOn with
    | tmul a c =>
      have ha0 : T a.val = 0 := hOT a.property
      simp only [TensorProduct.map_tmul,Submodule.subtype_apply,
        LinearMap.id_apply,ha0,zero_tmul]
    | add a c ha hc => simp only [map_add,ha,hc,add_zero]
  · intro i
    exact biformImage_output_weight O C hOh (hf i)

end Froberg
