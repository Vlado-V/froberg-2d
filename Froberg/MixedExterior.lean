import Froberg.PluckerCoordinates
import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing

/-! Mixed determinant constraints are linear in the actual Plücker coordinates. -/
noncomputable section
namespace Froberg.MixedExterior
open Module Matrix
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The exterior product of two decomposable vectors is the concatenated exterior product. -/
theorem wedge_ιMulti {r l : ℕ} (a : Fin r → V) (b : Fin l → V) :
    exteriorPower.wedge R V r l (exteriorPower.ιMulti R r a)
      (exteriorPower.ιMulti R l b) = exteriorPower.ιMulti R (r+l) (Fin.append a b) := by
  apply Subtype.ext
  exact ExteriorAlgebra.ιMulti_mul_ιMulti a b

variable {r l : ℕ}

/-- The determinant functional after adjoining the fixed final rows. -/
def mixedFunctional (b : Fin l → Fin (r+l) → R) :
    (⋀[R]^r (Fin (r+l) → R)) →ₗ[R] R :=
  (exteriorPower.alternatingMapLinearEquiv (Pi.basisFun R (Fin (r+l))).det).comp
    ((exteriorPower.wedge R (Fin (r+l) → R) r l).flip
      (exteriorPower.ιMulti R l b))

@[simp] theorem mixedFunctional_ιMulti (a : Fin r → Fin (r+l) → R)
    (b : Fin l → Fin (r+l) → R) :
    mixedFunctional b (exteriorPower.ιMulti R r a) =
      (Pi.basisFun R (Fin (r+l))).det (Fin.append a b) := by
  simp only [mixedFunctional, LinearMap.comp_apply, LinearMap.flip_apply,
    wedge_ιMulti, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

/-- Entries of the mixed-determinant constraint in the exterior basis. -/
def mixedRow (b : Fin l → Fin (r+l) → R) (I : Set.powersetCard (Fin (r+l)) r) : R :=
  mixedFunctional b ((Pi.basisFun R (Fin (r+l))).exteriorPower r I)

/-- The selected standard basis vectors in increasing coordinate order. -/
def basisVectors (I : Set.powersetCard (Fin (r+l)) r) : Fin r → Fin (r+l) → R :=
  (Pi.basisFun R (Fin (r+l))) ∘ Set.powersetCard.ofFinEmbEquiv.symm I

/-- The exterior constraint is literally a mixed determinant. -/
theorem mixedRow_apply (b : Fin l → Fin (r+l) → R)
    (I : Set.powersetCard (Fin (r+l)) r) :
    mixedRow b I = Matrix.det (Fin.append (basisVectors I) b) := by
  rw [mixedRow, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    mixedFunctional_ιMulti, Pi.basisFun_det_apply]
  rfl

/-- Coefficient specialization commutes with every mixed determinant. -/
theorem mixedRow_map {S : Type*} [CommRing S] (f : R →+* S)
    (b : Fin l → Fin (r+l) → R) (I : Set.powersetCard (Fin (r+l)) r) :
    mixedRow (fun i j => f (b i j)) I = f (mixedRow b I) := by
  rw [mixedRow_apply, mixedRow_apply]
  have he : (Matrix.of (Fin.append (basisVectors I) b)).map f =
      Fin.append (basisVectors I) (fun i j => f (b i j)) := by
    ext i j
    refine Fin.addCases (fun q => ?_) (fun q => ?_) i
    · simp [basisVectors, Pi.basisFun_apply, Matrix.map_apply, Pi.single_apply]
    · simp [Matrix.map_apply]
  rw [← he]
  exact (f.map_det _).symm

/-- Expanding in the exterior basis shows explicitly that every mixed determinant
is a linear equation in the Plücker coordinates, even over a coefficient ring. -/
theorem mixedRow_mul_plucker (a : Fin r → Fin (r+l) → R)
    (b : Fin l → Fin (r+l) → R) :
    (∑ I, mixedRow b I * pluckerCoordinates a I) =
      (Pi.basisFun R (Fin (r+l))).det (Fin.append a b) := by
  classical
  have h := congrArg (mixedFunctional b)
    (((Pi.basisFun R (Fin (r+l))).exteriorPower r).sum_repr
      (exteriorPower.ιMulti R r a))
  simp only [map_sum, map_smul, mixedFunctional_ιMulti, smul_eq_mul] at h
  change (∑ I, pluckerCoordinates a I * mixedRow b I) = _ at h
  calc
    (∑ I, mixedRow b I * pluckerCoordinates a I) =
        ∑ I, pluckerCoordinates a I * mixedRow b I :=
      Finset.sum_congr rfl (fun I _ => mul_comm _ _)
    _ = _ := h

/-- Vanishing of the actual concatenated exterior product gives the corresponding
linear constraint on the actual Plücker vector. -/
theorem mixedRow_constraint (a : Fin r → Fin (r+l) → R)
    (b : Fin l → Fin (r+l) → R)
    (hz : exteriorPower.ιMulti R (r+l) (Fin.append a b) = 0) :
    (∑ I, mixedRow b I * pluckerCoordinates a I) = 0 := by
  rw [mixedRow_mul_plucker, ← exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (Pi.basisFun R (Fin (r+l))).det, hz, map_zero]

/-- An invertible finite system of mixed determinants prevents simultaneous
failure for every nonzero exterior vector, hence uniformly for all subspaces. -/
theorem not_all_mixed_exterior_zero [IsDomain R]
    (b : Set.powersetCard (Fin (r+l)) r → Fin l → Fin (r+l) → R)
    (hdet : Matrix.det (fun I J => mixedRow (b I) J) ≠ 0)
    (a : Fin r → Fin (r+l) → R) (ha : pluckerCoordinates a ≠ 0) :
    ∃ I, exteriorPower.ιMulti R (r+l) (Fin.append a (b I)) ≠ 0 := by
  classical
  by_contra hn
  have hz : ∀ I, exteriorPower.ιMulti R (r+l) (Fin.append a (b I)) = 0 := by
    simpa only [not_exists, not_not] using hn
  have he : (fun I J => mixedRow (b I) J) *ᵥ pluckerCoordinates a = 0 := by
    funext I
    exact mixedRow_constraint a (b I) (hz I)
  apply ha
  exact Matrix.mulVec_injective_of_det_ne_zero hdet
    (he.trans (Matrix.mulVec_zero _).symm)

end Froberg.MixedExterior
