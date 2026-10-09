module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic

@[expose] public section

/-!
# Actual images of subspaces under bilinear multiplication

Varying a tuple of coefficients gives exactly the full bilinear image of the
span of its fixed vector tuple. These identities expose the actual subspaces
needed by relation and covector incidence charts.
-/
noncomputable section
namespace Quartic.BilinearImage
open Module
variable {K F V W : Type*} [Field K]
  [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
variable {ι : Type*} [Fintype ι]

/-- The span of all products of arbitrary coefficients and vectors in S. -/
def image (mu : F →ₗ[K] V →ₗ[K] W) (S : Submodule K V) : Submodule K W :=
  ⨆ f : F, S.map (mu f)

 theorem product_mem (mu : F →ₗ[K] V →ₗ[K] W) (S : Submodule K V)
    (f : F) (v : V) (hv : v ∈ S) : mu f v ∈ image mu S :=
  (le_iSup (fun f : F => S.map (mu f)) f) ⟨v, hv, rfl⟩

/-- The equation for a fixed tuple of vectors, with all coefficients variable. -/
def tupleMap (mu : F →ₗ[K] V →ₗ[K] W) (v : ι → V) : (ι → F) →ₗ[K] W :=
  ∑ i, (mu.flip (v i)).comp (LinearMap.proj i)

@[simp] theorem tupleMap_apply (mu : F →ₗ[K] V →ₗ[K] W) (v : ι → V) (f : ι → F) :
    tupleMap mu v f = ∑ i, mu (f i) (v i) := by simp [tupleMap]

/-- The tuple equation has exactly the full product image of its span. -/
theorem range_tupleMap (mu : F →ₗ[K] V →ₗ[K] W) (v : ι → V) :
    LinearMap.range (tupleMap mu v) = image mu (Submodule.span K (Set.range v)) := by
  classical
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    rw [tupleMap_apply]
    exact Submodule.sum_mem _ (fun i _ => product_mem mu _ (f i) (v i) (Submodule.subset_span ⟨i, rfl⟩))
  · apply iSup_le
    intro f
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    refine ⟨fun i => s i • f, ?_⟩
    simp only [tupleMap_apply, map_sum, map_smul, LinearMap.smul_apply]

/-- Scalar basis products span the actual full bilinear image. -/
theorem image_span_basis {κ : Type*} [Fintype κ] (b : Basis κ K F)
    (mu : F →ₗ[K] V →ₗ[K] W) (v : ι → V) :
    image mu (Submodule.span K (Set.range v)) =
      Submodule.span K (Set.range (fun p : ι × κ => mu (b p.2) (v p.1))) := by
  classical
  rw [← range_tupleMap]
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    rw [tupleMap_apply]
    apply Submodule.sum_mem
    intro i _
    rw [← b.sum_repr (f i), map_sum, LinearMap.sum_apply]
    apply Submodule.sum_mem
    intro j _
    rw [map_smul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i,j),rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i,j⟩,rfl⟩
    refine ⟨Pi.single i (b j), ?_⟩
    rw [tupleMap_apply, Finset.sum_eq_single i]
    · simp
    · intro k _ hki
      simp [Pi.single_eq_of_ne hki]
    · intro hn
      exact False.elim (hn (Finset.mem_univ i))

end Quartic.BilinearImage
