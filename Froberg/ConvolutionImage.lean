import Froberg.ConvolutionMap

/-! # The convolution image at a fixed distinct scalar tuple -/

noncomputable section
namespace Froberg
open Finset TensorProduct
variable {K : Type*} [Field K]

theorem moment_finset_homogeneous {ι : Type*} (a : ℕ) (t : ι → K) (s : Finset ι) :
    (∏ i ∈ s, momentLinear a (t i)).IsHomogeneous s.card := by
  simpa using MvPolynomial.IsHomogeneous.prod s (fun i => momentLinear a (t i))
    (fun _ => 1) (fun i _ => momentLinear_homogeneous a (t i))

theorem finset_prod_tmul {ι : Type*} (s : Finset ι) {A B : Type*}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] (f : ι → A) (g : ι → B) :
    (∏ i ∈ s, f i ⊗ₜ[K] g i) = (∏ i ∈ s, f i) ⊗ₜ[K] (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Algebra.TensorProduct.one_def]
  | @insert i s hi ih => simp only [Finset.prod_insert hi, ih, Algebra.TensorProduct.tmul_mul_tmul]

/-- Every subset-product tensor with the common full scalar product is in the actual image. -/
theorem convolution_subset_image {a e m : ℕ} (ha : 0 < a)
    (t : Fin (a + e - 1) → K) (I : ConvolutionSubset a e) :
    (momentProduct t I).val ⊗ₜ[K] (∏ i : Fin (a + e - 1), momentLinear m (t i)) ∈
      LinearMap.range (symmetricConvolutionMap (K := K) a e m) := by
  classical
  let f : Forms K (m + a - 1) e :=
    ⟨∏ i ∈ I.val, momentLinear (m + a - 1) (t i), by
      change (∏ i ∈ I.val, momentLinear (m + a - 1) (t i)).IsHomogeneous e
      simpa only [I.property] using moment_finset_homogeneous (m + a - 1) t I.val⟩
  let g : Forms K m (a - 1) :=
    ⟨∏ i ∈ I.valᶜ, momentLinear m (t i), by
      have hcard : I.valᶜ.card = a - 1 := by
        simp only [Finset.card_compl, Fintype.card_fin, I.property]
        omega
      change (∏ i ∈ I.valᶜ, momentLinear m (t i)).IsHomogeneous (a - 1)
      simpa only [hcard] using moment_finset_homogeneous m t I.valᶜ⟩
  refine ⟨f ⊗ₜ[K] g, ?_⟩
  rw [symmetricConvolutionMap_tmul]
  change convolutionHom a m (∏ i ∈ I.val, momentLinear (m + a - 1) (t i)) *
    (1 ⊗ₜ[K] (∏ i ∈ I.valᶜ, momentLinear m (t i))) = _
  rw [map_prod]
  simp_rw [convolutionHom_momentLinear]
  rw [finset_prod_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    Finset.prod_mul_prod_compl]
  rfl

@[simp] theorem momentProductsBasis_apply {a e : ℕ} (ha : 0 < a)
    (t : Fin (a + e - 1) → K) (ht : Function.Injective t) (I : ConvolutionSubset a e) :
    momentProductsBasis ha t ht I = momentProduct t I := by
  simp only [momentProductsBasis, coe_basisOfLinearIndependentOfCardEqFinrank']

/-- For a distinct scalar tuple, the entire output factor occurs alongside
its full scalar product. -/
theorem convolution_fixed_scalar_product {a e m : ℕ} (ha : 0 < a)
    (t : Fin (a + e - 1) → K) (ht : Function.Injective t) (v : Forms K a e) :
    v.val ⊗ₜ[K] (∏ i : Fin (a + e - 1), momentLinear m (t i)) ∈
      LinearMap.range (symmetricConvolutionMap (K := K) a e m) := by
  classical
  let y := ∏ i : Fin (a + e - 1), momentLinear m (t i)
  let L : Forms K a e →ₗ[K] BiformAlgebra K a m :=
    ((TensorProduct.mk K (Poly K a) (Poly K m)).flip y).comp
      (MvPolynomial.homogeneousSubmodule (Fin a) K e).subtype
  let B := momentProductsBasis ha t ht
  have hB : Submodule.span K (Set.range B) ≤
      (LinearMap.range (symmetricConvolutionMap (K := K) a e m)).comap L := by
    apply Submodule.span_le.mpr
    rintro w ⟨I, rfl⟩
    change (B I).val ⊗ₜ[K] y ∈ LinearMap.range (symmetricConvolutionMap (K := K) a e m)
    simpa only [B, y, momentProductsBasis_apply] using convolution_subset_image (m := m) ha t I
  rw [B.span_eq] at hB
  exact hB (Submodule.mem_top : v ∈ (⊤ : Submodule K (Forms K a e)))

end Froberg
