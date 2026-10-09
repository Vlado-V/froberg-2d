module

public import Quartic.ConvolutionBilinear
public import Quartic.ContractionBound

@[expose] public section

/-!
# The actual multiplication image and its annihilators

The linear image of a subspace of the first graded cokernel is the sum of
its images under multiplication by the variable basis. Its annihilator is
preserved by each corresponding dual contraction and by their evaluated
linear combinations. All dimensions below refer to these actual spaces.
-/

noncomputable section
namespace Quartic.ConvolutionImage
open ConvolutionPresentation ConvolutionDual ConvolutionInverse ConvolutionHilbert
open ConvolutionMultiplication ConvolutionEvaluation ConvolutionBilinear
open ConvolutionSymmetric
variable {K : Type*} [Field K] {t : ℕ}

/-- Multiplication of a subspace by the full variable space, in the actual cokernel. -/
def imageSpace (L : Submodule K (Cokernel K t 0)) : Submodule K (Cokernel K t 1) :=
  ⨆ i : Fin t, L.map (quotientMul (variableForm i))

/-- Every basis-variable multiple lies in the full multiplication image. -/
theorem variable_multiple_mem (L : Submodule K (Cokernel K t 0)) (i : Fin t)
    (x : Cokernel K t 0) (hx : x ∈ L) :
    quotientMul (variableForm i) x ∈ imageSpace L :=
  (le_iSup (fun i : Fin t => L.map (quotientMul (variableForm i))) i) ⟨x, hx, rfl⟩

/-- A functional annihilating the multiplication image contracts to a
functional annihilating the original subspace. -/
theorem variable_dual_mem (L : Submodule K (Cokernel K t 0))
    (φ : Module.Dual K (Cokernel K t 1)) (hφ : φ ∈ (imageSpace L).dualAnnihilator)
    (i : Fin t) : φ.comp (quotientMul (variableForm i)) ∈ L.dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator] at hφ ⊢
  intro x hx
  exact hφ _ (variable_multiple_mem L i x hx)

/-- The evaluated actual dual multiplication map. -/
def evaluatedDual (a : K) (φ : Module.Dual K (Cokernel K t 1)) :
    Module.Dual K (Cokernel K t 0) :=
  ∑ i : Fin t, a ^ i.val • φ.comp (quotientMul (variableForm i))

/-- Every evaluated contraction also annihilates the original subspace. -/
theorem evaluatedDual_mem (L : Submodule K (Cokernel K t 0))
    (φ : Module.Dual K (Cokernel K t 1)) (hφ : φ ∈ (imageSpace L).dualAnnihilator)
    (a : K) : evaluatedDual a φ ∈ L.dualAnnihilator := by
  exact Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ _ (variable_dual_mem L φ hφ i))

/-- Canonical duality takes the evaluated quotient transpose to the
corresponding actual presentation-annihilator contraction. -/
theorem evaluatedDual_cokernelDualEquiv (a : K)
    (φ : Module.Dual K (Cokernel K t 1)) :
    cokernelDualEquiv K t 0 (evaluatedDual a φ) =
      evaluatedContract a (cokernelDualEquiv K t 1 φ) := by
  simp only [evaluatedDual, evaluatedContract, map_sum, map_smul,
    dualContract_cokernelDualEquiv]
  rfl

/-- The symmetric family attached to the actual image annihilator. -/
def imageBilinearMap (ht : 2 ≤ t) (L : Submodule K (Cokernel K t 0)) :
    (imageSpace L).dualAnnihilator →ₗ[K]
      ((Fin (t - 1) → K) →ₗ[K] (Fin (t - 1) → K) →ₗ[K] K) :=
  bilinearMap.comp ((cokernelDualQuadraticEquiv ht).toLinearMap.comp
    (imageSpace L).dualAnnihilator.subtype)

/-- The symmetric family is faithful on the actual multiplication-image annihilator. -/
theorem imageBilinearMap_injective (ht : 2 ≤ t) (L : Submodule K (Cokernel K t 0)) :
    Function.Injective (imageBilinearMap ht L) :=
  bilinearMap_injective.comp ((cokernelDualQuadraticEquiv ht).injective.comp
    (Submodule.injective_subtype _))

theorem imageBilinearMap_symmetric (ht : 2 ≤ t) (L : Submodule K (Cokernel K t 0))
    (φ : (imageSpace L).dualAnnihilator) (x y : Fin (t - 1) → K) :
    imageBilinearMap ht L φ x y = imageBilinearMap ht L φ y x :=
  bilinearMap_symmetric _ x y

/-- The first annihilator dimension is exactly the codimension of the original subspace. -/
theorem source_annihilator_dimension (ht : 2 ≤ t) (L : Submodule K (Cokernel K t 0)) :
    Module.finrank K L + Module.finrank K L.dualAnnihilator = 2 * (t - 1) := by
  rw [Subspace.finrank_add_finrank_dualAnnihilator_eq, cokernel_degreeOne_finrank (by omega)]

/-- The image annihilator dimension is exactly the codimension of the actual multiplication image. -/
theorem image_annihilator_dimension (ht : 2 ≤ t) (L : Submodule K (Cokernel K t 0)) :
    Module.finrank K (imageSpace L) +
      Module.finrank K (imageSpace L).dualAnnihilator = t.choose 2 := by
  rw [Subspace.finrank_add_finrank_dualAnnihilator_eq, cokernel_degreeTwo_finrank ht]

end Quartic.ConvolutionImage
