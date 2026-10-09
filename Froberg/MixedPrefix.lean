module

public import Froberg.UniversalMixedPosition
public import Froberg.PrefixExterior

@[expose] public section

/-! Uniform mixed minors prevent too many independent blocks from failing. -/
noncomputable section
namespace Froberg.MixedExterior
open Module
variable {K α : Type*} [Field K] {r l : ℕ}

/-- An independent tuple has a nonzero vector of actual Plücker coordinates. -/
theorem independent_pluckerCoordinates_ne_zero {n : ℕ}
    (a : Fin r → Fin n → K) (ha : LinearIndependent K a) :
    pluckerCoordinates a ≠ 0 := by
  simpa only [Module.Basis.coe_span_apply] using
    (basis_pluckerCoordinates_ne_zero (Submodule.span K (Set.range a))
      (Module.Basis.span ha))

/-- A nonzero mixed minor guarantees that at least one of the selected prefixes
extends any fixed independent tuple independently. -/
theorem exists_independent_prefix
    (t : Set.powersetCard (Fin (r+l)) r → ℕ) (ht : ∀ I, t I ≤ l)
    (label : (Σ I, Fin (t I)) → α) (v : α → Fin (r+l) → K)
    (hdet : Matrix.det (fun I J => mixedRow (paddedVectors t label v I) J) ≠ 0)
    (a : Fin r → Fin (r+l) → K) (ha : LinearIndependent K a) :
    ∃ I, LinearIndependent K (Fin.append a (fun j : Fin (t I) => v (label ⟨I,j⟩))) := by
  obtain ⟨I,hI⟩ := not_all_mixed_exterior_zero (paddedVectors t label v) hdet a
    (independent_pluckerCoordinates_ne_zero a ha)
  have hi : LinearIndependent K (Fin.append a (paddedVectors t label v I)) := by
    by_contra hdep
    exact hI (AlternatingMap.map_linearDependent _ _ hdep)
  have hp := ProjectionFailure.independent_append_prefix (ht I) a
    (paddedVectors t label v I) hi
  have he : paddedVectors t label v I ∘ Fin.castLE (ht I) =
      fun j : Fin (t I) => v (label ⟨I,j⟩) := by
    funext j
    simp only [Function.comp_apply, paddedVectors, Fin.val_castLE, j.isLt, dite_true]
  exact ⟨I,he ▸ hp⟩

/-- The universal polynomial condition is uniform over every independent tuple,
not just a previously selected subspace. -/
theorem universal_exists_independent_prefix {h : ℕ}
    (v : α → Fin h → K) (hv : UniversalMixedPosition v)
    (r : Fin (h+1))
    (t : Set.powersetCard (Fin (r.val+(h-r.val))) r.val → Fin ((h-r.val)+1))
    (label : (Σ I, Fin (t I).val) ↪ α)
    (a : Fin r.val → Fin (r.val+(h-r.val)) → K) (ha : LinearIndependent K a) :
    ∃ I, LinearIndependent K (Fin.append a
      (fun j : Fin (t I).val => fun x =>
        v (label ⟨I,j⟩) (Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt_succ r.isLt)) x))) := by
  exact exists_independent_prefix (fun I => (t I).val)
    (fun I => Nat.le_of_lt_succ (t I).isLt) label _ (hv ⟨r,t,label⟩) a ha

end Froberg.MixedExterior
