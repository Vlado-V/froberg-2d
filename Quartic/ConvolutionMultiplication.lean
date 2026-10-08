import Quartic.ConvolutionInverse

/-!
# Actual multiplication and dual contraction in the convolution module

Multiplication by a homogeneous linear polynomial commutes with the
presentation. It therefore descends to the actual graded cokernels and its
transpose preserves the actual presentation annihilators. These maps supply
the multiplication/contraction operations used by the uniform image bounds.
-/

noncomputable section
namespace Quartic.ConvolutionMultiplication
open MvPolynomial ConvolutionPresentation ConvolutionDual
variable {K : Type*} [Field K] {t j : ℕ}

/-- Multiply a homogeneous form by an actual linear polynomial. -/
def formMul (a : Quartic.Forms K t 1) :
    Quartic.Forms K t j →ₗ[K] Quartic.Forms K t (j + 1) where
  toFun b := ⟨a.val * b.val, by
    change IsHomogeneous (a.val * b.val) (j + 1)
    simpa only [Nat.add_comm] using a.property.mul b.property⟩
  map_add' _ _ := Subtype.ext (mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (mul_smul_comm _ _ _)

/-- Multiply every output row by the same linear polynomial. -/
def targetMul (a : Quartic.Forms K t 1) : Target K t j →ₗ[K] Target K t (j + 1) :=
  LinearMap.pi fun d => (formMul a).comp (LinearMap.proj d)

/-- Multiply every input column by the same linear polynomial. -/
def sourceMul (a : Quartic.Forms K t 1) : Source K t j →ₗ[K] Source K t (j + 1) :=
  LinearMap.pi fun k => (formMul a).comp (LinearMap.proj k)

@[simp] theorem targetMul_apply_val (a : Quartic.Forms K t 1)
    (b : Target K t j) (d : Fin 3) : (targetMul a b d).val = a.val * (b d).val := rfl

@[simp] theorem sourceMul_apply_val (a : Quartic.Forms K t 1)
    (b : Source K t j) (k : Fin (t + 2)) : (sourceMul a b k).val = a.val * (b k).val := rfl

/-- Multiplication respects the actual convolution relations. -/
theorem presentation_mul_commutes (a : Quartic.Forms K t 1) (b : Source K t j) :
    presentation (sourceMul a b) = targetMul a (presentation b) := by
  funext d
  apply Subtype.ext
  simp only [presentation_apply_val, sourceMul_apply_val, targetMul_apply_val,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The image of the relation space is contained in the next relation space. -/
theorem targetMul_maps_relations (a : Quartic.Forms K t 1) :
    LinearMap.range (presentation (K := K) (t := t) (j := j)) ≤
      (LinearMap.range (presentation (K := K) (t := t) (j := j + 1))).comap (targetMul a) := by
  rintro _ ⟨b, rfl⟩
  exact ⟨sourceMul a b, presentation_mul_commutes a b⟩

/-- Actual multiplication on adjacent positive-degree graded cokernels. -/
def quotientMul (a : Quartic.Forms K t 1) : Cokernel K t j →ₗ[K] Cokernel K t (j + 1) :=
  Submodule.mapQ _ _ (targetMul a) (targetMul_maps_relations a)

@[simp] theorem quotientMul_mk (a : Quartic.Forms K t 1) (b : Target K t (j + 1)) :
    quotientMul a (Submodule.Quotient.mk b) = Submodule.Quotient.mk (targetMul a b) := rfl

/-- The transpose of actual multiplication preserves the dual relation spaces. -/
theorem dualContract_mem (a : Quartic.Forms K t 1)
    (φ : Module.Dual K (Target K t (j + 1 + 1)))
    (hφ : φ ∈ annihilator K t (j + 1)) :
    φ.comp (targetMul a) ∈ annihilator K t j := by
  apply (mem_annihilator_iff _).mpr
  intro b
  change φ (targetMul a (presentation b)) = 0
  rw [← presentation_mul_commutes]
  exact (mem_annihilator_iff φ).mp hφ (sourceMul a b)

/-- Contraction is the transpose of an actual quotient multiplication map. -/
def dualContract (a : Quartic.Forms K t 1) :
    annihilator K t (j + 1) →ₗ[K] annihilator K t j where
  toFun φ := ⟨φ.val.comp (targetMul a), dualContract_mem a φ.val φ.property⟩
  map_add' φ ψ := by rfl
  map_smul' a φ := by rfl

/-- The canonical quotient-dual identifications intertwine the two maps. -/
theorem dualContract_cokernelDualEquiv (a : Quartic.Forms K t 1)
    (φ : Module.Dual K (Cokernel K t (j + 1))) :
    dualContract a (cokernelDualEquiv K t (j + 1) φ) =
      cokernelDualEquiv K t j (φ.comp (quotientMul a)) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro b
  rfl

end Quartic.ConvolutionMultiplication
