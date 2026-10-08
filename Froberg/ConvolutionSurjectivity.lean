import Froberg.ConvolutionImage
import Mathlib.RingTheory.Flat.Basic

/-! # Convolution reaches the full separated homogeneous target -/

noncomputable section
namespace Froberg
open Finset TensorProduct
variable {K : Type*} [Field K]

/-- A scalar basis product of degree `a+e-1` is in the convolution image
with every degree-`e` output form. -/
theorem convolution_scalar_basis_image {a e m : ℕ} (ha : 0 < a)
    (t : Fin (m + (a + e - 1) - 1) → K) (ht : Function.Injective t)
    (J : ConvolutionSubset m (a + e - 1)) (v : Forms K a e) :
    v.val ⊗ₜ[K] (momentProduct t J).val ∈
      LinearMap.range (symmetricConvolutionMap (K := K) a e m) := by
  classical
  let E : J.val ≃ Fin (a + e - 1) := Finset.equivFinOfCardEq J.property
  let tJ : Fin (a + e - 1) → K := fun i => t (E.symm i).val
  have htJ : Function.Injective tJ := by
    intro i j hij
    have h := ht hij
    exact E.symm.injective (Subtype.ext h)
  have hprod : (∏ i : Fin (a + e - 1), momentLinear m (tJ i)) = (momentProduct t J).val := by
    change (∏ i : Fin (a + e - 1), momentLinear m (t (E.symm i).val)) =
      ∏ j ∈ J.val, momentLinear m (t j)
    calc
      _ = ∏ j : J.val, momentLinear m (t j.val) :=
        Fintype.prod_equiv E.symm _ _ (fun _ => rfl)
      _ = _ := Finset.prod_coe_sort J.val (fun j => momentLinear m (t j))
  simpa only [hprod] using convolution_fixed_scalar_product (m := m) ha tJ htJ v

/-- Every pure tensor in the claimed homogeneous target is reached. -/
theorem convolution_all_pure_tensors [Infinite K] {a e m : ℕ}
    (ha : 0 < a) (hm : 0 < m) (v : Forms K a e) (w : Forms K m (a + e - 1)) :
    v.val ⊗ₜ[K] w.val ∈ LinearMap.range (symmetricConvolutionMap (K := K) a e m) := by
  classical
  let t : Fin (m + (a + e - 1) - 1) → K := fun i => Infinite.natEmbedding K i.val
  have ht : Function.Injective t := (Infinite.natEmbedding K).injective.comp Fin.val_injective
  let B := momentProductsBasis hm t ht
  let L : Forms K m (a + e - 1) →ₗ[K] BiformAlgebra K a m :=
    ((TensorProduct.mk K (Poly K a) (Poly K m)) v.val).comp
      (MvPolynomial.homogeneousSubmodule (Fin m) K (a + e - 1)).subtype
  have hB : Submodule.span K (Set.range B) ≤
      (LinearMap.range (symmetricConvolutionMap (K := K) a e m)).comap L := by
    apply Submodule.span_le.mpr
    rintro x ⟨J, rfl⟩
    change v.val ⊗ₜ[K] (B J).val ∈ LinearMap.range (symmetricConvolutionMap (K := K) a e m)
    simpa only [B, momentProductsBasis_apply] using convolution_scalar_basis_image ha t ht J v
  rw [B.span_eq] at hB
  exact hB (Submodule.mem_top : w ∈ (⊤ : Submodule K (Forms K m (a + e - 1))))

/-- Inclusion of the tensor product of the two homogeneous components into
the polynomial tensor algebra. -/
def biformInclusion (a m e N : ℕ) :
    (Forms K a e ⊗[K] Forms K m N) →ₗ[K] BiformAlgebra K a m :=
  TensorProduct.map (MvPolynomial.homogeneousSubmodule (Fin a) K e).subtype
    (MvPolynomial.homogeneousSubmodule (Fin m) K N).subtype

theorem biformInclusion_injective (a m e N : ℕ) :
    Function.Injective (biformInclusion (K := K) a m e N) :=
  TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Subtype.val_injective

/-- The image of the concrete convolution map contains the entire claimed target. -/
theorem biform_range_le_convolution_range [Infinite K] {a e m : ℕ}
    (ha : 0 < a) (hm : 0 < m) :
    LinearMap.range (biformInclusion (K := K) a m e (a + e - 1)) ≤
      LinearMap.range (symmetricConvolutionMap (K := K) a e m) := by
  rintro x ⟨w, rfl⟩
  induction w using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul v w => exact convolution_all_pure_tensors ha hm v w
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

end Froberg
