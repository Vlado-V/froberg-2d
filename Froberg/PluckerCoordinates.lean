module

public import Froberg.ExteriorMatrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

/-!
# Plücker coordinates of an actual invariant subspace

These coordinates are computed by minors.  A semilinear transformation
preserving a subspace preserves the line of the coordinates of any basis.
-/

namespace Froberg

open Matrix Module

variable {R : Type*} [CommRing R] {n r : ℕ}

/-- Coordinates of the exterior product of a tuple of vectors. -/
noncomputable def pluckerCoordinates (v : Fin r → Fin n → R) :
    Set.powersetCard (Fin n) r → R :=
  ((Pi.basisFun R (Fin n)).exteriorPower r).repr (exteriorPower.ιMulti R r v)

/-- Plücker coordinates are minors, hence polynomials in the entries. -/
theorem pluckerCoordinates_apply (v : Fin r → Fin n → R)
    (s : Set.powersetCard (Fin n) r) :
    pluckerCoordinates v s =
      (Matrix.of fun i j : Fin r => v i (Set.powersetCard.ofFinEmbEquiv.symm s j)).det := by
  rw [pluckerCoordinates, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1

/-- The compound matrix gives the action on Plücker coordinates. -/
theorem pluckerCoordinates_mulVec (A : Matrix (Fin n) (Fin n) R)
    (v : Fin r → Fin n → R) :
    exteriorMatrix r A *ᵥ pluckerCoordinates v =
      pluckerCoordinates (fun i => A *ᵥ v i) := by
  unfold pluckerCoordinates
  rw [exteriorMatrix_mulVec_repr, exteriorPower.map_apply_ιMulti]
  rfl

/-- Plücker coordinates commute with homomorphisms of coefficient rings. -/
theorem pluckerCoordinates_map {S : Type*} [CommRing S] (f : R →+* S)
    (v : Fin r → Fin n → R) :
    pluckerCoordinates (fun i j => f (v i j)) = fun s => f (pluckerCoordinates v s) := by
  funext s
  rw [pluckerCoordinates_apply, pluckerCoordinates_apply]
  exact (f.map_det _).symm

section Field

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- The exterior product of a basis is nonzero, as its determinant is one. -/
theorem basis_wedge_ne_zero (b : Basis (Fin r) K E) :
    exteriorPower.ιMulti K r b ≠ 0 := by
  intro h
  have hh := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) h
  exact one_ne_zero (by simpa only [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    b.det_self, map_zero] using hh)

/-- A basis of a subspace has a nonzero tuple of Plücker coordinates. -/
theorem basis_pluckerCoordinates_ne_zero
    (U : Submodule K (Fin n → K)) (b : Basis (Fin r) K U) :
    pluckerCoordinates (fun i => (b i : Fin n → K)) ≠ 0 := by
  intro h
  have hw : exteriorPower.ιMulti K r (fun i => (b i : Fin n → K)) = 0 := by
    apply ((Pi.basisFun K (Fin n)).exteriorPower r).repr.injective
    ext s
    simpa only [pluckerCoordinates, map_zero, Finsupp.zero_apply, Pi.zero_apply] using congrFun h s
  have hw' : exteriorPower.map r U.subtype (exteriorPower.ιMulti K r b) = 0 := by
    simpa only [exteriorPower.map_apply_ιMulti, Function.comp_def, Submodule.subtype_apply] using hw
  apply basis_wedge_ne_zero b
  exact (exteriorPower.map_injective_field U.injective_subtype)
    (by simpa only [map_zero] using hw')

/-- Every tuple in a subspace of dimension `r` has Plücker coordinates
proportional to those of a basis of that subspace. -/
theorem pluckerCoordinates_subspace_proportional
    (U : Submodule K (Fin n → K)) (b : Basis (Fin r) K U)
    (v : Fin r → U) :
    ∃ c : K, pluckerCoordinates (fun i => (v i : Fin n → K)) =
      c • pluckerCoordinates (fun i => (b i : Fin n → K)) := by
  have hdim : finrank K U = r := by simpa using finrank_eq_card_basis b
  have hext : finrank K (⋀[K]^r U) = 1 := by simp [exteriorPower.finrank_eq, hdim]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
    (exteriorPower.ιMulti K r b) (basis_wedge_ne_zero b)).mp hext
      (exteriorPower.ιMulti K r v)
  refine ⟨c, ?_⟩
  have ha := congrArg (exteriorPower.map r U.subtype) hc
  simp only [map_smul, exteriorPower.map_apply_ιMulti] at ha
  funext s
  have hr := congrArg (fun x => ((Pi.basisFun K (Fin n)).exteriorPower r).repr x s) ha
  simpa [pluckerCoordinates, Function.comp_def] using hr.symm

/-- A semilinear transformation preserving an actual subspace preserves
its actual Plücker line.  No invariant-line hypothesis is needed. -/
theorem semilinear_pluckerCoordinates_proportional
    (U : Submodule K (Fin n → K)) (b : Basis (Fin r) K U)
    (e : K ≃+* K) (A : Matrix (Fin n) (Fin n) K)
    (hU : ∀ v ∈ U, A *ᵥ (fun i => e (v i)) ∈ U) :
    ∃ c : K,
      exteriorMatrix r A *ᵥ
        (fun s => e (pluckerCoordinates (fun i => (b i : Fin n → K)) s)) =
      c • pluckerCoordinates (fun i => (b i : Fin n → K)) := by
  let v : Fin r → U := fun i =>
    ⟨A *ᵥ (fun j => e ((b i : Fin n → K) j)), hU (b i) (b i).property⟩
  obtain ⟨c, hc⟩ := pluckerCoordinates_subspace_proportional U b v
  refine ⟨c, ?_⟩
  have he : pluckerCoordinates (fun i j => e ((b i : Fin n → K) j)) =
      fun s => e (pluckerCoordinates (fun i => (b i : Fin n → K)) s) :=
    pluckerCoordinates_map e.toRingHom _
  rw [← he, pluckerCoordinates_mulVec]
  exact hc

end Field

end Froberg
