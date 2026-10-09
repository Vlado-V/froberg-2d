module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic

@[expose] public section

/-!
# Maximal rank by adjoining auxiliary target vectors

A map to a j-dimensional target has maximal possible rank if adjoining
j-h auxiliary columns makes it surjective, where h is its source dimension.
Surjectivity is expressed exactly as exclusion of a common nonzero covector.
These are concrete linear-algebra implications for the incidence construction,
not an assumption that any such auxiliary columns or motions exist.
-/
noncomputable section
namespace Quartic.AuxiliarySurjectivity
open Module
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The actual map with e additional freely chosen target columns. -/
def augment {e : ℕ} (F : V →ₗ[K] W) (Z : Fin e → W) :
    (V × (Fin e → K)) →ₗ[K] W :=
  F.coprod (∑ i, (LinearMap.proj i).smulRight (Z i))

@[simp] theorem augment_apply {e : ℕ} (F : V →ₗ[K] W) (Z : Fin e → W)
    (v : V) (c : Fin e → K) : augment F Z (v, c) = F v + ∑ i, c i • Z i := by
  simp [augment]

/-- A covector kills the augmented map exactly when it kills F and every
additional column. -/
theorem covector_comp_eq_zero_iff {e : ℕ} (F : V →ₗ[K] W) (Z : Fin e → W)
    (ell : W →ₗ[K] K) :
    ell.comp (augment F Z) = 0 ↔ ell.comp F = 0 ∧ ∀ i, ell (Z i) = 0 := by
  classical
  constructor
  · intro h
    constructor
    · apply LinearMap.ext
      intro v
      have hv := LinearMap.congr_fun h (v, 0)
      simpa using hv
    · intro i
      have hi := LinearMap.congr_fun h (0, Pi.single i 1)
      simpa using hi
  · rintro ⟨hF, hZ⟩
    apply LinearMap.ext
    rintro ⟨v, c⟩
    have hv := LinearMap.congr_fun hF v
    simpa [map_sum, hZ] using hv

/-- The exact covector exclusion formulation of surjectivity. -/
theorem surjective_iff_covectors {e : ℕ} (F : V →ₗ[K] W) (Z : Fin e → W) :
    Function.Surjective (augment F Z) ↔
      ∀ ell : W →ₗ[K] K, ell.comp F = 0 → (∀ i, ell (Z i) = 0) → ell = 0 := by
  rw [← LinearMap.dualMap_injective_iff, ← LinearMap.ker_eq_bot,
    LinearMap.ker_eq_bot']
  change (∀ ell : W →ₗ[K] K, ell.comp (augment F Z) = 0 → ell = 0) ↔ _
  simp only [covector_comp_eq_zero_iff, and_imp]

/-- Surjectivity after adjoining e columns forces the original rank to miss
the full target dimension by at most e. -/
theorem target_finrank_le_rank_add [FiniteDimensional K V] [FiniteDimensional K W]
    {e : ℕ} (F : V →ₗ[K] W) (Z : Fin e → W)
    (h : Function.Surjective (augment F Z)) :
    finrank K W ≤ finrank K (LinearMap.range F) + e := by
  let G : (Fin e → K) →ₗ[K] W := ∑ i, (LinearMap.proj i).smulRight (Z i)
  have hrange : LinearMap.range F ⊔ LinearMap.range G = ⊤ := by
    rw [← LinearMap.range_coprod]
    exact LinearMap.range_eq_top.mpr h
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range F) (LinearMap.range G)
  rw [hrange, finrank_top] at hdim
  have hg : finrank K (LinearMap.range G) ≤ e := by
    simpa using G.finrank_range_le
  omega

/-- Choosing exactly the target-source dimension difference as the auxiliary
column count turns common-covector exclusion into maximal rank. -/
theorem maximal_rank_of_covector_exclusion [FiniteDimensional K V] [FiniteDimensional K W]
    (F : V →ₗ[K] W) (Z : Fin (finrank K W - finrank K V) → W)
    (h : ∀ ell : W →ₗ[K] K, ell.comp F = 0 → (∀ i, ell (Z i) = 0) → ell = 0) :
    finrank K (LinearMap.range F) = min (finrank K V) (finrank K W) := by
  have hs := (surjective_iff_covectors F Z).mpr h
  have ht := target_finrank_le_rank_add F Z hs
  have hv := F.finrank_range_le
  have hw := (LinearMap.range F).finrank_le
  omega

end Quartic.AuxiliarySurjectivity
