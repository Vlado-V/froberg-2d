module

public import Froberg.ConvolutionSurjectivity
public import Froberg.FiniteImageEquivalence
public import Froberg.TargetCoverage

@[expose] public section

/-! # Symmetric-power convolution: the full isomorphism of Lemma B.6

The source map is the explicit coefficient convolution `φ(l_j)=Σ_{i+k=j}v_i y_k`.
The proof uses two finite Vandermonde product bases and the exact dimension
identity. It works over every infinite field.
-/

noncomputable section
namespace Froberg
open Module TensorProduct
variable {K : Type*} [Field K] [Infinite K]

omit [Infinite K] in
theorem symmetricConvolution_dimensions {a e m : ℕ} (ha : 0 < a) (hm : 0 < m) :
    finrank K (Forms K (m + a - 1) e ⊗[K] Forms K m (a - 1)) =
      finrank K (Forms K a e ⊗[K] Forms K m (a + e - 1)) := by
  rw [finrank_tensorProduct, finrank_tensorProduct,
    finrank_forms K (m + a - 1) e (by omega), finrank_forms K m (a - 1) hm,
    finrank_forms K a e ha, finrank_forms K m (a + e - 1) hm]
  rw [show m + a - 1 + e - 1 = m + a + e - 2 by omega,
    show m + (a - 1) - 1 = m + a - 2 by omega,
    show m + (a + e - 1) - 1 = m + a + e - 2 by omega]
  exact convolution_dimension_identity hm ha

/-- The explicit convolution map is an isomorphism onto the full homogeneous tensor target. -/
theorem exists_symmetricConvolutionEquiv {a e m : ℕ} (ha : 0 < a) (hm : 0 < m) :
    ∃ E : (Forms K (m + a - 1) e ⊗[K] Forms K m (a - 1)) ≃ₗ[K]
      (Forms K a e ⊗[K] Forms K m (a + e - 1)),
      ∀ x, biformInclusion a m e (a + e - 1) (E x) = symmetricConvolutionMap a e m x := by
  apply exists_linearEquiv_of_equal_dimension_range (K := K)
    (symmetricConvolutionMap (K := K) a e m) (biformInclusion (K := K) a m e (a + e - 1))
  · exact biformInclusion_injective a m e _
  · exact biform_range_le_convolution_range ha hm
  · exact symmetricConvolution_dimensions ha hm

/-- The convolution isomorphism, with its map characterized by the actual bilinear coefficients. -/
def symmetricConvolutionEquiv {a e m : ℕ} (ha : 0 < a) (hm : 0 < m) :
    (Forms K (m + a - 1) e ⊗[K] Forms K m (a - 1)) ≃ₗ[K]
      (Forms K a e ⊗[K] Forms K m (a + e - 1)) :=
  Classical.choose (exists_symmetricConvolutionEquiv ha hm)

theorem symmetricConvolutionEquiv_apply {a e m : ℕ} (ha : 0 < a) (hm : 0 < m)
    (x : Forms K (m + a - 1) e ⊗[K] Forms K m (a - 1)) :
    biformInclusion a m e (a + e - 1) (symmetricConvolutionEquiv ha hm x) =
      symmetricConvolutionMap a e m x :=
  Classical.choose_spec (exists_symmetricConvolutionEquiv ha hm) x

theorem symmetricConvolutionEquiv_tmul {a e m : ℕ} (ha : 0 < a) (hm : 0 < m)
    (f : Forms K (m + a - 1) e) (g : Forms K m (a - 1)) :
    biformInclusion a m e (a + e - 1) (symmetricConvolutionEquiv ha hm (f ⊗ₜ[K] g)) =
      convolutionHom a m f.val * (1 ⊗ₜ[K] g.val) := by
  rw [symmetricConvolutionEquiv_apply, symmetricConvolutionMap_tmul]

end Froberg
