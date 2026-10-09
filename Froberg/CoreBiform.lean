module

public import Froberg.PreparedBackground
public import Froberg.PolynomialTensorTransport
public import Quartic.SplitTensor

@[expose] public section

/-! Weighted X-degree extraction equals the actual tensor biform component. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct
open Quartic.FreeCoefficients Quartic.FreeMonomialCounts Quartic.SplitBigrading
variable {K : Type} [Field K] {h m i j : ℕ}

@[simp] theorem coreWeight_merge (a : Fin h →₀ ℕ) (b : Fin m →₀ ℕ) :
    Finsupp.weight (coreWeight h m) (mergeExponent a b) = a.degree := by
  rw [Finsupp.weight_eq_sum,Fin.sum_univ_add,Finsupp.degree_eq_sum]
  simp [coreWeight]

/-- Taking a free-variable coefficient commutes with X-degree extraction. -/
theorem freeCoeff_coreComponent (b : Fin m →₀ ℕ) (p : Poly K (h+m)) (i : ℕ) :
    freeCoeff b (coreComponent h m i p) = homogeneousComponent i (freeCoeff b p) := by
  ext a
  simp [coreComponent,freeCoeff_coeff,coeff_weightedHomogeneousComponent,
    coeff_homogeneousComponent,Finsupp.degree_eq_weight_one]

/-- Every biform has the expected X-weight. -/
theorem coreComponent_blockPolynomial (u : Block K h m i j) (k : ℕ) :
    coreComponent h m k (blockPolynomial u) = if k=i then blockPolynomial u else 0 := by
  apply sub_eq_zero.mp
  apply eq_zero_of_freeCoeff
  intro b
  rw [map_sub,freeCoeff_coreComponent]
  by_cases hb : b.degree = j
  · let b' : ExactExponent m j := ⟨b,hb⟩
    have he : freeCoeff b (blockPolynomial u) = (u b').val := freeCoeff_blockPolynomial u b'
    rw [he]
    simp only [homogeneousComponent_of_mem (u b').property]
    split_ifs <;> simp_all
  · rw [freeCoeff_blockPolynomial_of_degree_ne u b hb,map_zero]
    split_ifs
    · rw [freeCoeff_blockPolynomial_of_degree_ne u b hb,sub_self]
    · simp

/-- The total-degree component projects onto its genuine tensor biform. -/
theorem coreComponent_exists_block (p : Forms K (h+m) (i+j)) :
    ∃ u : Block K h m i j, coreComponent h m i p.val = blockPolynomial u := by
  let u : Block K h m i j := fun b => ⟨freeCoeff b.val p.val, by
    change (freeCoeff b.val p.val).IsHomogeneous i
    simpa only [b.property,Nat.add_sub_cancel] using freeCoeff_homogeneous p.val p.property b.val⟩
  refine ⟨u,?_⟩
  apply sub_eq_zero.mp
  apply eq_zero_of_freeCoeff
  intro b
  rw [map_sub,freeCoeff_coreComponent]
  by_cases hb : b.degree = j
  · let b' : ExactExponent m j := ⟨b,hb⟩
    have he : freeCoeff b (blockPolynomial u) = (u b').val := freeCoeff_blockPolynomial u b'
    rw [he]
    exact sub_eq_zero.mpr (homogeneousComponent_eq_self (u b').property)
  · rw [freeCoeff_blockPolynomial_of_degree_ne u b hb,sub_zero]
    by_cases hd : b.degree ≤ i+j
    · have hp := freeCoeff_homogeneous p.val p.property b
      rw [homogeneousComponent_of_mem hp,if_neg]
      omega
    · rw [freeCoeff_eq_zero_of_degree_lt p.val p.property b (by omega),map_zero]

/-- The ambient image of the actual tensor product of the two form spaces. -/
def ambientBiform : (Forms K h i ⊗[K] Forms K m j) →ₗ[K] Poly K (h+m) :=
  (Forms K (h+m) (i+j)).subtype.comp Quartic.SplitTensor.polynomialEmbedding

theorem ambientBiform_eq_block : ambientBiform (K := K) (h := h) (m := m) (i := i) (j := j) =
    blockPolynomial.comp Quartic.SplitTensor.biformEquiv.toLinearMap := rfl

/-- The low-component coefficient space is exactly the actual biform tensor
image, including degrees zero and one. -/
theorem coreCoefficientSpace_eq_biform_range :
    coreCoefficientSpace K h m (i+j) i =
      (ambientBiform (K := K) (h := h) (m := m) (i := i) (j := j)).range := by
  ext p
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨u,hu⟩ := coreComponent_exists_block (⟨p,hp⟩ : Forms K (h+m) (i+j))
    refine ⟨Quartic.SplitTensor.biformEquiv.symm u,?_⟩
    rw [ambientBiform_eq_block,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply,← hu]
  · rintro ⟨v,rfl⟩
    refine ⟨ambientBiform v,?_,?_⟩
    · exact (Quartic.SplitTensor.polynomialEmbedding v).property
    · rw [ambientBiform_eq_block,LinearMap.comp_apply,coreComponent_blockPolynomial,if_pos rfl]

/-- The biform embedding is exactly the split polynomial algebra equivalence. -/
theorem ambientBiform_eq_split :
    ambientBiform (K := K) (h := h) (m := m) (i := i) (j := j) =
      (splitPolynomialEquiv (K := K) h m).toLinearMap.comp
        (TensorProduct.map (Forms K h i).subtype (Forms K m j).subtype) := by
  apply TensorProduct.ext
  ext x y : 2
  change (Quartic.SplitTensor.polynomialEmbedding (x ⊗ₜ[K] y)).val =
    splitPolynomialEquiv (K := K) h m (x.val ⊗ₜ[K] y.val)
  simp only [ambientBiform,LinearMap.comp_apply,Submodule.subtype_apply,
    Quartic.SplitTensor.polynomialEmbedding_tmul_val,TensorProduct.map_tmul,
    LinearEquiv.coe_coe,AlgEquiv.toLinearMap_apply,splitPolynomialEquiv_tmul]

/-- Exact tensor-algebra description of every X-degree coefficient space. -/
theorem coreCoefficientSpace_eq_split_range :
    coreCoefficientSpace K h m (i+j) i =
      ((splitPolynomialEquiv (K := K) h m).toLinearMap.comp
        (TensorProduct.map (Forms K h i).subtype (Forms K m j).subtype)).range := by
  rw [coreCoefficientSpace_eq_biform_range,ambientBiform_eq_split]

end Froberg
