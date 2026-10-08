import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Pi

/-!
# Coordinates for finite-dimensional bilinear families

Changing the source and target of a bilinear family to finite coordinates
preserves the dimension of every image and the injectivity of each flipped
map. The parameter space is left unchanged, so it can be a tuple of actual
polynomial coefficients in applications.
-/

noncomputable section
namespace Quartic.PolynomialBilinearCoordinates
open Module

variable {K U V W V' W' : Type*} [Field K]
variable [AddCommGroup U] [Module K U]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']

/-- Conjugation of the two value spaces, preserving the parameter space. -/
def conjugate (eV : V ≃ₗ[K] V') (eW : W ≃ₗ[K] W')
    (B : U →ₗ[K] V →ₗ[K] W) : U →ₗ[K] V' →ₗ[K] W' where
  toFun u := eW.toLinearMap.comp ((B u).comp eV.symm.toLinearMap)
  map_add' u v := by ext x; simp
  map_smul' c u := by ext x; simp

@[simp] theorem conjugate_apply (eV : V ≃ₗ[K] V') (eW : W ≃ₗ[K] W')
    (B : U →ₗ[K] V →ₗ[K] W) (u : U) (x : V') :
    conjugate eV eW B u x = eW (B u (eV.symm x)) := rfl

/-- The coordinate image is exactly the image of the original range under the target equivalence. -/
theorem range_conjugate (eV : V ≃ₗ[K] V') (eW : W ≃ₗ[K] W')
    (B : U →ₗ[K] V →ₗ[K] W) (u : U) :
    LinearMap.range (conjugate eV eW B u) =
      (LinearMap.range (B u)).map eW.toLinearMap := by
  change LinearMap.range (eW.toLinearMap.comp ((B u).comp eV.symm.toLinearMap)) = _
  rw [LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ eV.symm.range]

/-- Range dimension is unchanged by these actual linear equivalences. -/
theorem finrank_range_conjugate (eV : V ≃ₗ[K] V') (eW : W ≃ₗ[K] W')
    (B : U →ₗ[K] V →ₗ[K] W) (u : U) :
    finrank K (LinearMap.range (conjugate eV eW B u)) =
      finrank K (LinearMap.range (B u)) := by
  rw [range_conjugate, eW.finrank_map_eq]

/-- Injectivity in the parameter variable is preserved at the corresponding source point. -/
theorem injective_flip_conjugate_iff (eV : V ≃ₗ[K] V') (eW : W ≃ₗ[K] W')
    (B : U →ₗ[K] V →ₗ[K] W) (x : V') :
    Function.Injective ((conjugate eV eW B).flip x) ↔
      Function.Injective (B.flip (eV.symm x)) := by
  constructor
  · intro h u v huv
    apply h
    exact congrArg eW huv
  · intro h u v huv
    apply h
    exact eW.injective huv

/-- Injectivity in the source variable is likewise unchanged. -/
theorem injective_conjugate_iff (eV : V ≃ₗ[K] V') (eW : W ≃ₗ[K] W')
    (B : U →ₗ[K] V →ₗ[K] W) (u : U) :
    Function.Injective (conjugate eV eW B u) ↔ Function.Injective (B u) := by
  constructor
  · intro h x y hxy
    apply eV.injective
    apply h
    simpa only [conjugate_apply, LinearEquiv.symm_apply_apply] using congrArg eW hxy
  · intro h x y hxy
    apply eV.symm.injective
    exact h (eW.injective hxy)

variable [FiniteDimensional K V] [FiniteDimensional K W]

/-- The chosen finite coordinate equivalence of an actual vector space. -/
def coordinates (K : Type*) [Field K] (V : Type*)
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    V ≃ₗ[K] (Fin (finrank K V) → K) := (Module.finBasis K V).equivFun

/-- The coordinate bilinear family used by polynomial matrix avoidance. -/
def coordinate (B : U →ₗ[K] V →ₗ[K] W) :
    U →ₗ[K] (Fin (finrank K V) → K) →ₗ[K] (Fin (finrank K W) → K) :=
  conjugate (coordinates K V) (coordinates K W) B

@[simp] theorem coordinate_apply (B : U →ₗ[K] V →ₗ[K] W) (u : U)
    (x : Fin (finrank K V) → K) :
    coordinate B u x = coordinates K W (B u ((coordinates K V).symm x)) := rfl

theorem finrank_range_coordinate (B : U →ₗ[K] V →ₗ[K] W) (u : U) :
    finrank K (LinearMap.range (coordinate B u)) = finrank K (LinearMap.range (B u)) :=
  finrank_range_conjugate _ _ B u

theorem injective_flip_coordinate_iff (B : U →ₗ[K] V →ₗ[K] W)
    (x : Fin (finrank K V) → K) :
    Function.Injective ((coordinate B).flip x) ↔
      Function.Injective (B.flip ((coordinates K V).symm x)) :=
  injective_flip_conjugate_iff _ _ B x

theorem injective_flip_coordinate_at (B : U →ₗ[K] V →ₗ[K] W) (x : V) :
    Function.Injective ((coordinate B).flip (coordinates K V x)) ↔
      Function.Injective (B.flip x) := by
  simpa only [LinearEquiv.symm_apply_apply] using
    injective_flip_coordinate_iff B (coordinates K V x)

theorem injective_coordinate_iff (B : U →ₗ[K] V →ₗ[K] W) (u : U) :
    Function.Injective (coordinate B u) ↔ Function.Injective (B u) :=
  injective_conjugate_iff _ _ B u

variable [FiniteDimensional K U] {q : ℕ}

/-- Coordinates are decoded independently in every entry of the relation tuple. -/
def tupleDecode (K : Type*) [Field K] (U : Type*)
    [AddCommGroup U] [Module K U] [FiniteDimensional K U] (q : ℕ) :
    (Fin q → Fin (finrank K U) → K) ≃ₗ[K] (Fin q → U) :=
  LinearEquiv.piCongrRight (fun _ => (coordinates K U).symm)

@[simp] theorem tupleDecode_apply (F : Fin q → Fin (finrank K U) → K) (i : Fin q) :
    tupleDecode K U q F i = (coordinates K U).symm (F i) := rfl

@[simp] theorem tupleDecode_ne_zero_iff (F : Fin q → Fin (finrank K U) → K) :
    tupleDecode K U q F ≠ 0 ↔ F ≠ 0 := (tupleDecode K U q).map_ne_zero_iff

/-- Tuple span is transported by the actual inverse coordinate equivalence. -/
theorem span_tupleDecode (F : Fin q → Fin (finrank K U) → K) :
    Submodule.span K (Set.range (tupleDecode K U q F)) =
      (Submodule.span K (Set.range F)).map (coordinates K U).symm.toLinearMap := by
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem finrank_span_tupleDecode (F : Fin q → Fin (finrank K U) → K) :
    finrank K (Submodule.span K (Set.range (tupleDecode K U q F))) =
      finrank K (Submodule.span K (Set.range F)) := by
  rw [span_tupleDecode, LinearEquiv.finrank_map_eq]

/-- Coordinates on the relation entries, coefficient space, and target space. -/
def tupleCoordinate (B : (Fin q → U) →ₗ[K] V →ₗ[K] W) :
    (Fin q → Fin (finrank K U) → K) →ₗ[K]
      (Fin (finrank K V) → K) →ₗ[K] (Fin (finrank K W) → K) :=
  (coordinate B).comp (tupleDecode K U q).toLinearMap

@[simp] theorem tupleCoordinate_apply (B : (Fin q → U) →ₗ[K] V →ₗ[K] W)
    (F : Fin q → Fin (finrank K U) → K) (x : Fin (finrank K V) → K) :
    tupleCoordinate B F x =
      coordinates K W (B (tupleDecode K U q F) ((coordinates K V).symm x)) := rfl

theorem finrank_range_tupleCoordinate (B : (Fin q → U) →ₗ[K] V →ₗ[K] W)
    (F : Fin q → Fin (finrank K U) → K) :
    finrank K (LinearMap.range (tupleCoordinate B F)) =
      finrank K (LinearMap.range (B (tupleDecode K U q F))) :=
  finrank_range_coordinate B _

/-- Full coordinate injectivity is exactly injectivity for actual relation tuples. -/
theorem injective_flip_tupleCoordinate_iff (B : (Fin q → U) →ₗ[K] V →ₗ[K] W)
    (x : Fin (finrank K V) → K) :
    Function.Injective ((tupleCoordinate B).flip x) ↔
      Function.Injective (B.flip ((coordinates K V).symm x)) := by
  constructor
  · intro h F G hFG
    have he : (tupleDecode K U q).symm F = (tupleDecode K U q).symm G := by
      apply h
      change coordinates K W (B (tupleDecode K U q ((tupleDecode K U q).symm F))
        ((coordinates K V).symm x)) =
        coordinates K W (B (tupleDecode K U q ((tupleDecode K U q).symm G))
          ((coordinates K V).symm x))
      simpa only [LinearEquiv.apply_symm_apply, LinearMap.flip_apply] using
        congrArg (coordinates K W) hFG
    exact (tupleDecode K U q).symm.injective he
  · intro h F G hFG
    apply (tupleDecode K U q).injective
    exact h ((coordinates K W).injective hFG)

end Quartic.PolynomialBilinearCoordinates
