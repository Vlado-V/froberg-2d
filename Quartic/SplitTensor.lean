module

public import Quartic.SplitBigrading
public import Quartic.ConvolutionFreeMultiplication
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

/-!
# Tensor coordinates for actual polynomial bidegrees

The tensor product of the two homogeneous polynomial spaces is identified
with the coefficient model already embedded in the full polynomial ring.
The quotient kernel and the overlap of the two families of relations are
proved directly, without dimension or independence premises.
-/
noncomputable section
namespace Quartic.SplitTensor
open Module MvPolynomial FreeMonomialCounts FreeCoefficients
open scoped TensorProduct
variable {K : Type*} [Field K]

section Exactness
variable {X Y : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- Relations from the first factor. -/
def leftRelations (P : Submodule K X) : Submodule K (X ⊗[K] Y) :=
  LinearMap.range (TensorProduct.map P.subtype (LinearMap.id : Y →ₗ[K] Y))

/-- Relations from the second factor. -/
def rightRelations (Q : Submodule K Y) : Submodule K (X ⊗[K] Y) :=
  LinearMap.range (TensorProduct.map (LinearMap.id : X →ₗ[K] X) Q.subtype)

/-- Relations common to both factors. -/
def jointRelations (P : Submodule K X) (Q : Submodule K Y) : Submodule K (X ⊗[K] Y) :=
  LinearMap.range (TensorProduct.map P.subtype Q.subtype)

/-- The kernel of quotienting both factors consists exactly of the two relation images. -/
theorem quotient_kernel (P : Submodule K X) (Q : Submodule K Y) :
    (TensorProduct.map P.mkQ Q.mkQ).ker = leftRelations P ⊔ rightRelations Q := by
  have h := TensorProduct.map_ker (LinearMap.exact_subtype_mkQ P) P.mkQ_surjective
    (LinearMap.exact_subtype_mkQ Q) Q.mkQ_surjective
  change (TensorProduct.map P.mkQ Q.mkQ).ker = rightRelations Q ⊔ leftRelations P at h
  exact h.trans (sup_comm _ _)

/-- The intersection is exactly the tensor product of the two relation spaces. -/
theorem relations_intersection (P : Submodule K X) (Q : Submodule K Y) :
    leftRelations P ⊓ rightRelations Q = jointRelations P Q := by
  apply le_antisymm
  · rintro z ⟨⟨u, rfl⟩, hz⟩
    have hz0 : TensorProduct.map (LinearMap.id : X →ₗ[K] X) Q.mkQ
        (TensorProduct.map P.subtype (LinearMap.id : Y →ₗ[K] Y) u) = 0 := by
      have hk : (TensorProduct.map (LinearMap.id : X →ₗ[K] X) Q.mkQ).ker =
          rightRelations Q := lTensor_mkQ X Q
      exact (show rightRelations Q ≤
        (TensorProduct.map (LinearMap.id : X →ₗ[K] X) Q.mkQ).ker by
          rw [hk]) hz
    have hcomm : TensorProduct.map (LinearMap.id : X →ₗ[K] X) Q.mkQ ∘ₗ
        TensorProduct.map P.subtype (LinearMap.id : Y →ₗ[K] Y) =
        TensorProduct.map P.subtype (LinearMap.id : (Y ⧸ Q) →ₗ[K] Y ⧸ Q) ∘ₗ
          TensorProduct.map (LinearMap.id : P →ₗ[K] P) Q.mkQ := by
      ext x y
      simp
    have hu0 : TensorProduct.map (LinearMap.id : P →ₗ[K] P) Q.mkQ u = 0 := by
      have hi := Module.Flat.rTensor_preserves_injective_linearMap (M := Y ⧸ Q)
        P.subtype P.subtype_injective
      apply hi
      rw [map_zero]
      exact (congrArg (fun f : P ⊗[K] Y →ₗ[K] X ⊗[K] (Y ⧸ Q) => f u) hcomm).symm.trans hz0
    have hu : u ∈ LinearMap.range
        (TensorProduct.map (LinearMap.id : P →ₗ[K] P) Q.subtype) := by
      have hk : (TensorProduct.map (LinearMap.id : P →ₗ[K] P) Q.mkQ).ker =
          LinearMap.range (TensorProduct.map (LinearMap.id : P →ₗ[K] P) Q.subtype) :=
        lTensor_mkQ P Q
      rw [← hk]
      exact hu0
    obtain ⟨v, rfl⟩ := hu
    refine ⟨v, ?_⟩
    have he : TensorProduct.map P.subtype (LinearMap.id : Y →ₗ[K] Y) ∘ₗ
        TensorProduct.map (LinearMap.id : P →ₗ[K] P) Q.subtype =
        TensorProduct.map P.subtype Q.subtype := by ext x y; simp
    exact (congrArg (fun f => f v) he).symm
  · rintro z ⟨u, rfl⟩
    constructor
    · refine ⟨TensorProduct.map (LinearMap.id : P →ₗ[K] P) Q.subtype u, ?_⟩
      have he : TensorProduct.map P.subtype (LinearMap.id : Y →ₗ[K] Y) ∘ₗ
          TensorProduct.map (LinearMap.id : P →ₗ[K] P) Q.subtype =
          TensorProduct.map P.subtype Q.subtype := by ext x y; simp
      exact congrArg (fun f => f u) he
    · refine ⟨TensorProduct.map P.subtype (LinearMap.id : Q →ₗ[K] Q) u, ?_⟩
      have he : TensorProduct.map (LinearMap.id : X →ₗ[K] X) Q.subtype ∘ₗ
          TensorProduct.map P.subtype (LinearMap.id : Q →ₗ[K] Q) =
          TensorProduct.map P.subtype Q.subtype := by ext x y; simp
      exact congrArg (fun f => f u) he

/-- Actual finite sums of products with a fixed first-factor family. -/
def sumTensorLeft {I : Type*} [Fintype I] (v : I → X) : (I → Y) →ₗ[K] X ⊗[K] Y :=
  ∑ i, (TensorProduct.mk K X Y (v i)).comp (LinearMap.proj i)

@[simp] theorem sumTensorLeft_apply {I : Type*} [Fintype I] (v : I → X) (a : I → Y) :
    sumTensorLeft v a = ∑ i, v i ⊗ₜ[K] a i := by simp [sumTensorLeft]

/-- These finite product sums fill exactly the first-factor relation image. -/
theorem sumTensorLeft_range {I : Type*} [Fintype I] (v : I → X) :
    LinearMap.range (sumTensorLeft (Y := Y) v) =
      leftRelations (Submodule.span K (Set.range v)) := by
  apply le_antisymm
  · rintro z ⟨a, rfl⟩
    refine ⟨∑ i, (⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ : Submodule.span K (Set.range v))
      ⊗ₜ[K] a i, ?_⟩
    simp
  · rintro z ⟨u, rfl⟩
    induction u using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp x.property
      refine ⟨fun i => a i • y, ?_⟩
      simp only [TensorProduct.map_tmul, Submodule.subtype_apply, LinearMap.id_apply]
      rw [sumTensorLeft_apply, ← ha, TensorProduct.sum_tmul]
      apply Finset.sum_congr rfl
      intro i _
      simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    | add u v hu hv => simpa only [map_add] using (LinearMap.range _).add_mem hu hv

/-- Actual finite sums of products with a fixed second-factor family. -/
def sumTensorRight {I : Type*} [Fintype I] (v : I → Y) : (I → X) →ₗ[K] X ⊗[K] Y :=
  (TensorProduct.comm K Y X).toLinearMap.comp (sumTensorLeft v)

@[simp] theorem sumTensorRight_apply {I : Type*} [Fintype I] (v : I → Y) (a : I → X) :
    sumTensorRight v a = ∑ i, a i ⊗ₜ[K] v i := by simp [sumTensorRight]

/-- These finite product sums fill exactly the second-factor relation image. -/
theorem sumTensorRight_range {I : Type*} [Fintype I] (v : I → Y) :
    LinearMap.range (sumTensorRight (X := X) v) =
      rightRelations (Submodule.span K (Set.range v)) := by
  rw [sumTensorRight, LinearMap.range_comp, sumTensorLeft_range]
  unfold leftRelations rightRelations
  rw [← LinearMap.range_comp]
  have he : (TensorProduct.comm K Y X).toLinearMap ∘ₗ
      TensorProduct.map (Submodule.span K (Set.range v)).subtype (LinearMap.id : X →ₗ[K] X) =
      TensorProduct.map (LinearMap.id : X →ₗ[K] X) (Submodule.span K (Set.range v)).subtype ∘ₗ
        (TensorProduct.comm K (Submodule.span K (Set.range v)) X).toLinearMap := by
    ext x y
    simp
  rw [he, LinearMap.range_comp]
  simp

end Exactness
section Biform
variable {t w i j : ℕ}

/-- Actual monomial coefficient coordinates in a homogeneous polynomial space. -/
def exponentCoordinates : Forms K w j ≃ₗ[K] (ExactExponent w j → K) := by
  classical
  let f : Forms K w j →ₗ[K] (ExactExponent w j → K) :=
    LinearMap.pi fun b => (lcoeff K b.val).comp (Forms K w j).subtype
  apply LinearEquiv.ofBijective f
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply MvPolynomial.ext
    intro b
    by_cases hb : b.degree = j
    · exact congrFun hpq ⟨b, hb⟩
    · rw [p.property.coeff_eq_zero hb, q.property.coeff_eq_zero hb]
  · intro a
    let p : Forms K w j := ∑ b : ExactExponent w j,
      ⟨monomial b.val (a b), isHomogeneous_monomial (a b) b.property⟩
    refine ⟨p, ?_⟩
    funext b
    change p.val.coeff b.val = a b
    simp only [p, Submodule.coe_sum]
    simp only [coeff_sum, coeff_monomial]
    have he (e : ExactExponent w j) : e.val = b.val ↔ e = b := Subtype.ext_iff.symm
    simp_rw [he]
    simp

@[simp] theorem exponentCoordinates_apply (p : Forms K w j) (b : ExactExponent w j) :
    exponentCoordinates p b = p.val.coeff b.val := rfl

/-- Reconstruct a homogeneous polynomial from its degree-exact monomials. -/
theorem homogeneous_monomial_sum (y : Forms K w j) :
    y.val = ∑ b : ExactExponent w j, monomial b.val (y.val.coeff b.val) := by
  classical
  apply MvPolynomial.ext
  intro e
  simp only [coeff_sum, coeff_monomial]
  by_cases he : e.degree = j
  · let b : ExactExponent w j := ⟨e, he⟩
    have heq (a : ExactExponent w j) : a.val = e ↔ a = b := by
      change a.val = b.val ↔ a = b
      exact Subtype.ext_iff.symm
    simp_rw [heq]
    simp [b]
  · rw [y.property.coeff_eq_zero he]
    symm
    apply Finset.sum_eq_zero
    intro b _
    rw [ite_eq_right]
    intro h
    exact False.elim (he (h ▸ b.property))

/-- Renaming a child monomial inserts zero core exponents. -/
theorem child_rename_exponent (b : Fin w →₀ ℕ) :
    b.mapDomain (Fin.natAdd t) = mergeExponent (0 : Fin t →₀ ℕ) b := by
  ext s
  refine Fin.addCases ?_ ?_ s
  · intro k
    rw [Finsupp.mapDomain_of_notMem_range]
    · simp
    · rintro ⟨l, hl⟩
      have h := congrArg Fin.val hl
      simp at h
      omega
  · intro k
    rw [Finsupp.mapDomain_apply_of_injective (Fin.natAdd_injective w t)]
    simp

/-- Tensor products of actual forms give exactly the actual biform coefficient model. -/
def biformEquiv : (Forms K t i ⊗[K] Forms K w j) ≃ₗ[K] SplitBigrading.Block K t w i j := by
  classical
  exact (TensorProduct.congr (LinearEquiv.refl K _) exponentCoordinates).trans
    (TensorProduct.piScalarRight K K (Forms K t i) (ExactExponent w j))

@[simp] theorem biformEquiv_tmul (x : Forms K t i) (y : Forms K w j)
    (b : ExactExponent w j) : biformEquiv (x ⊗ₜ[K] y) b = y.val.coeff b.val • x := by
  simp [biformEquiv, TensorProduct.piScalarRight_apply]

/-- Embed a tensor biform into the full homogeneous polynomial space. -/
def polynomialEmbedding : (Forms K t i ⊗[K] Forms K w j) →ₗ[K] Forms K (t + w) (i + j) :=
  SplitBigrading.embed.comp biformEquiv.toLinearMap

/-- A pure tensor is the actual product of the two renamed polynomial factors. -/
@[simp] theorem polynomialEmbedding_tmul_val (x : Forms K t i) (y : Forms K w j) :
    (polynomialEmbedding (x ⊗ₜ[K] y)).val =
      rename (Fin.castAdd w) x.val * rename (Fin.natAdd t) y.val := by
  classical
  change SplitBigrading.blockPolynomial (biformEquiv (x ⊗ₜ[K] y)) = _
  rw [SplitBigrading.blockPolynomial_apply]
  simp only [biformEquiv_tmul, Submodule.coe_smul, map_smul]
  conv_rhs => rw [homogeneous_monomial_sum y, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [ConvolutionFreeMultiplication.liftCoeff_eq_mul, rename_monomial, child_rename_exponent]
  rw [← mul_smul_comm, smul_monomial, smul_eq_mul, mul_one]

theorem polynomialEmbedding_injective : Function.Injective
    (polynomialEmbedding (K := K) (t := t) (w := w) (i := i) (j := j)) :=
  SplitBigrading.embed_injective.comp biformEquiv.injective

/-- The tensor model fills precisely its asserted bidegree component. -/
theorem polynomialEmbedding_range : LinearMap.range
    (polynomialEmbedding (K := K) (t := t) (w := w) (i := i) (j := j)) =
    SplitBigrading.bidegreeSpace K t w i j := by
  rw [polynomialEmbedding, LinearMap.range_comp]
  simp [SplitBigrading.bidegreeSpace]

end Biform
end Quartic.SplitTensor
