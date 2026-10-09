module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Tactic

@[expose] public section

/-!
# The determinant line inside an exterior power

For every finite-dimensional subspace, its top exterior power injects into
the corresponding exterior power of the ambient space.  Its image is a
one-dimensional subspace and behaves naturally under linear maps.
-/

namespace Froberg

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- The Plücker line of a subspace is the image of its top exterior power. -/
noncomputable def pluckerLine (U : Submodule K E) :
    Submodule K (⋀[K]^(finrank K U) E) :=
  LinearMap.range (exteriorPower.map (finrank K U) U.subtype)

/-- The determinant image is a line, including for the zero subspace. -/
theorem pluckerLine_finrank (U : Submodule K E) :
    finrank K (pluckerLine U) = 1 := by
  unfold pluckerLine
  rw [LinearMap.finrank_range_of_inj
    (exteriorPower.map_injective_field U.injective_subtype)]
  simp

/-- Every subspace has a nonzero Plücker vector. -/
theorem pluckerLine_exists_ne_zero (U : Submodule K E) :
    ∃ v : ⋀[K]^(finrank K U) E, v ∈ pluckerLine U ∧ v ≠ 0 := by
  have : Nontrivial (pluckerLine U) := Module.nontrivial_of_finrank_pos
    (by rw [pluckerLine_finrank]; exact Nat.zero_lt_one)
  obtain ⟨v, hv⟩ := exists_ne (0 : pluckerLine U)
  refine ⟨v, v.property, ?_⟩
  exact fun h => hv (Subtype.ext h)

/-- Every nonzero Plücker vector spans the determinant line. -/
theorem pluckerLine_scalar_multiple
    (U : Submodule K E) (v : ⋀[K]^(finrank K U) E)
    (hv : v ∈ pluckerLine U) (hv0 : v ≠ 0)
    {w : ⋀[K]^(finrank K U) E} (hw : w ∈ pluckerLine U) :
    ∃ c : K, c • v = w := by
  have hv0' : (⟨v, hv⟩ : pluckerLine U) ≠ 0 := by
    intro h
    exact hv0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
    (⟨v, hv⟩ : pluckerLine U) hv0').mp (pluckerLine_finrank U) ⟨w, hw⟩
  exact ⟨c, congrArg Subtype.val hc⟩

omit [FiniteDimensional K E] in
/-- A map preserving a subspace also preserves its actual Plücker line. -/
theorem map_mem_pluckerLine
    (U : Submodule K E) (f : E →ₗ[K] E)
    (hf : ∀ x ∈ U, f x ∈ U)
    {v : ⋀[K]^(finrank K U) E} (hv : v ∈ pluckerLine U) :
    exteriorPower.map (finrank K U) f v ∈ pluckerLine U := by
  obtain ⟨w, rfl⟩ := hv
  refine ⟨exteriorPower.map (finrank K U) (f.restrict hf) w, ?_⟩
  have heq : U.subtype ∘ₗ f.restrict hf = f ∘ₗ U.subtype := by
    ext x
    rfl
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, heq,
    exteriorPower.map_comp, LinearMap.comp_apply]

omit [FiniteDimensional K E] in
/-- On the `r`th exterior power, scalar multiplication by `a` induces
scalar multiplication by `a^r`. -/
theorem exteriorPower_map_smul_id (r : ℕ) (a : K) :
    exteriorPower.map r (a • (LinearMap.id : E →ₗ[K] E)) =
      a ^ r • (LinearMap.id : (⋀[K]^r E) →ₗ[K] (⋀[K]^r E)) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, exteriorPower.map_apply_ιMulti,
    LinearMap.smul_apply, LinearMap.id_apply]
  simpa [Function.comp_def] using (exteriorPower.ιMulti K r).map_smul_univ (fun _ => a) v

omit [FiniteDimensional K E] in
/-- A scalar ambient map acts on the Plücker line with the exponent equal
to the dimension of the subspace. -/
theorem pluckerLine_scalar_action
    (U : Submodule K E) (a : K) (v : ⋀[K]^(finrank K U) E) :
    exteriorPower.map (finrank K U) (a • (LinearMap.id : E →ₗ[K] E)) v =
      a ^ finrank K U • v := by
  rw [exteriorPower_map_smul_id]
  rfl

omit [FiniteDimensional K E] in
/-- If a nonzero determinant vector is fixed and the ambient action has
weight `e`, a root of unity of order `l` forces `l ∣ e * dim U`. -/
theorem pluckerLine_fixed_scalar_divisibility
    (U : Submodule K E) {l e : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ l)
    (v : ⋀[K]^(finrank K U) E) (hv0 : v ≠ 0)
    (hfixed : exteriorPower.map (finrank K U)
      (ζ ^ e • (LinearMap.id : E →ₗ[K] E)) v = v) :
    l ∣ e * finrank K U := by
  apply (hζ.pow_eq_one_iff_dvd _).mp
  apply smul_left_injective K hv0
  simpa only [pluckerLine_scalar_action, ← pow_mul, one_smul] using hfixed

end Froberg
