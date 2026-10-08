import Froberg.TensorFormCoordinates
import Froberg.OrderedMonomialWeights
import Froberg.WeightedBilinearGrowth

/-! The dimension ratio of an actual bilinear image is preserved after
multiplying by homogeneous forms. This is the tensorization used in C.3/C.4. -/
noncomputable section
namespace Froberg
open Module TensorProduct Quartic.HomogeneousCoefficientCoordinates
open Quartic.WeightedInitialImage
variable {K B V W : Type*} [Field K]
  [AddCommGroup B] [Module K B] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
variable {m e d : ℕ}
attribute [local instance] tensorFormGroup

/-- Conjugating both spaces by their monomial coordinates preserves the
complete span of actual products. -/
theorem tensorFormImage_coordinates (μ : B →ₗ[K] V →ₗ[K] W)
    (L : Submodule K (V ⊗[K] Forms K m e)) :
    (Quartic.BilinearImage.image (tensorFormProduct (d := d) μ) L).map
      orderedTensorFormCoordinates.toLinearMap =
      multiplicationImage (orderedTensorFormProduct μ)
        (L.map orderedTensorFormCoordinates.toLinearMap) := by
  classical
  rw [Quartic.BilinearImage.image,Submodule.map_iSup,multiplicationImage]
  apply le_antisymm
  · apply iSup_le
    intro f
    apply le_trans _ (le_iSup _ (tensorFormCoordinates f))
    rw [← Submodule.map_comp,← Submodule.map_comp]
    apply le_of_eq
    congr 1
    ext x
    simp [orderedTensorFormProduct]
  · apply iSup_le
    intro f
    apply le_trans _ (le_iSup _ (tensorFormCoordinates.symm f))
    rw [← Submodule.map_comp,← Submodule.map_comp]
    apply le_of_eq
    congr 1
    ext x
    simp [orderedTensorFormProduct]

/-- A uniform bound for a bilinear image tensorizes with the exact homogeneous
polynomial dimension ratio. All products are the literal tensor products of
μ and homogeneous multiplication. -/
theorem tensorized_bilinear_growth [Module.Finite K V] [Module.Finite K W]
    (μ : B →ₗ[K] V →ₗ[K] W) (hm : 0 < m) (A B₀ : ℕ)
    (hμ : ∀ S : Submodule K V,
      B₀ * finrank K S ≤ A * finrank K (Quartic.BilinearImage.image μ S))
    (L : Submodule K (V ⊗[K] Forms K m e)) :
    B₀ * (m+e+d-1).choose (e+d) * finrank K L ≤
      A * (m+e-1).choose e *
        finrank K (Quartic.BilinearImage.image (tensorFormProduct (d := d) μ) L) := by
  have h := weighted_bilinear_growth μ (orderedTensorFormProduct (m := m) (e := e) (d := d) μ)
    OrderedMonomials.shift OrderedMonomials.shift_strictMono
    (orderedTensorFormProduct_single μ) orderedMonomialWeight
    ((e+d).choose e) ((m+e+d-1).choose d)
    orderedMonomialWeight_row (orderedMonomialWeight_column hm)
    (Nat.choose_pos (Nat.le_add_right e d)) orderedMonomialWeight_support A B₀ hμ
    (L.map orderedTensorFormCoordinates.toLinearMap)
  rw [← tensorFormImage_coordinates,
    orderedTensorFormCoordinates.finrank_map_eq,
    orderedTensorFormCoordinates.finrank_map_eq] at h
  simpa only [card_coefficient_exponent,Nat.add_assoc] using h

end Froberg
