module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

@[expose] public section

/-! Functorial changes of the finite output space of a polynomial vector. -/
noncomputable section
namespace Froberg
open TensorProduct
open scoped Classical
variable {K : Type*} [Field K]
variable {I J H : Type*} [Fintype I] [Fintype J] [Fintype H]
variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Apply a linear change of output coordinates without changing coefficients. -/
def vectorOutputMap (L : (I → K) →ₗ[K] (J → K)) : (I → V) →ₗ[K] (J → V) :=
  (piScalarRight K K V J).toLinearMap.comp
    ((TensorProduct.map LinearMap.id L).comp (piScalarRight K K V I).symm.toLinearMap)

@[simp] theorem vectorOutputMap_pure (L : (I → K) →ₗ[K] (J → K))
    (v : I → K) (c : V) :
    vectorOutputMap L (fun i => v i • c) = fun j => L v j • c := by
  have hi : (piScalarRight K K V I).symm (fun i => v i • c)=c ⊗ₜ[K] v := by
    apply (piScalarRight K K V I).injective
    simp [piScalarRightHom_tmul]
  simp only [vectorOutputMap,LinearMap.comp_apply,LinearEquiv.coe_coe,hi,
    TensorProduct.map_tmul,LinearMap.id_apply,piScalarRight_apply,piScalarRightHom_tmul]

@[simp] theorem vectorOutputMap_comp
    (L : (I → K) →ₗ[K] (J → K)) (M : (J → K) →ₗ[K] (H → K)) :
    (vectorOutputMap (V := V) M).comp (vectorOutputMap L) = vectorOutputMap (M.comp L) := by
  apply LinearMap.ext
  intro p
  obtain ⟨z,rfl⟩ := (piScalarRight K K V I).surjective p
  induction z using TensorProduct.inductionOn with
  | tmul c v => simp [piScalarRightHom_tmul,vectorOutputMap_pure,LinearMap.comp_apply]
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (·+·) hz hz'

@[simp] theorem vectorOutputMap_id :
    vectorOutputMap (V := V) (LinearMap.id (R := K) (M := I → K)) = LinearMap.id := by
  apply LinearMap.ext
  intro p
  obtain ⟨z,rfl⟩ := (piScalarRight K K V I).surjective p
  induction z using TensorProduct.inductionOn with
  | tmul c v => simp [piScalarRightHom_tmul]
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (·+·) hz hz'

/-- Coefficient maps commute with output maps. -/
theorem vectorOutputMap_natural (L : (I → K) →ₗ[K] (J → K)) (f : V →ₗ[K] W) (p : I → V) :
    vectorOutputMap L (fun i => f (p i)) = fun j => f (vectorOutputMap L p j) := by
  obtain ⟨z,rfl⟩ := (piScalarRight K K V I).surjective p
  induction z using TensorProduct.inductionOn with
  | tmul c v => simp [piScalarRightHom_tmul,map_smul,vectorOutputMap_pure]
  | add z z' hz hz' =>
    simp only [map_add,Pi.add_apply]
    change vectorOutputMap L ((fun i => f (piScalarRight K K V I z i)) +
      (fun i => f (piScalarRight K K V I z' i))) = _
    rw [map_add,hz,hz']
    rfl

/-- No information is lost when the output-space map is injective. -/
theorem vectorOutputMap_injective (L : (I → K) →ₗ[K] (J → K))
    (hL : Function.Injective L) : Function.Injective (vectorOutputMap (V := V) L) :=
  (piScalarRight K K V J).injective.comp
    ((TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id hL).comp
      (piScalarRight K K V I).symm.injective)

end Froberg
