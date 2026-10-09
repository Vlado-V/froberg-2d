module

public import Quartic.PolynomialRankOpen
public import Mathlib.LinearAlgebra.Dimension.Free

@[expose] public section

/-! A single linear projection is injective on any finite family of subspaces
whose dimensions fit in its target. The simultaneous condition is open. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial Quartic
variable {K V W I : Type*} [Field K] [Infinite K] [Fintype I]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The individual restriction dimension bounds give a common nonempty
principal open of projections, with no assumed general-position witness. -/
theorem finite_subspace_projection_open (U : I → Submodule K V)
    (hU : ∀ i, finrank K (U i) ≤ finrank K W) :
    ∃ D : MvPolynomial (Fin (finrank K (V →ₗ[K] W))) K,
      (∃ x, eval x D ≠ 0) ∧ ∀ x, eval x D ≠ 0 → ∀ i,
        Function.Injective (((Module.finBasis K (V →ₗ[K] W)).equivFun.symm x).comp (U i).subtype) := by
  classical
  let b := Module.finBasis K (V →ₗ[K] W)
  have hi (i : I) : ∃ L : V →ₗ[K] W, Function.Injective (L.comp (U i).subtype) := by
    obtain ⟨j,hj⟩ := finrank_le_iff_exists_linearMap.mp (hU i)
    obtain ⟨p,hp⟩ := (U i).subtype.exists_leftInverse_of_injective (U i).ker_subtype
    refine ⟨j.comp p,?_⟩
    have he : (j.comp p).comp (U i).subtype=j := by
      rw [LinearMap.comp_assoc,hp,LinearMap.comp_id]
    rwa [he]
  have hlocal (i : I) :
      ∃ D : MvPolynomial (Fin (finrank K (V →ₗ[K] W))) K,
        (∃ x, eval x D ≠ 0) ∧ ∀ x, eval x D ≠ 0 →
          Function.Injective ((b.equivFun.symm x).comp (U i).subtype) := by
    obtain ⟨L,hL⟩ := hi i
    let A := fun x => (b.equivFun.symm x).comp (U i).subtype
    have hA : IsPolynomialFamily A := by
      apply isPolynomialFamily_linearMap
      intro u
      exact isPolynomialFamily_linear ((LinearMap.applyₗ (R := K) (M₂ := W) u.val).comp
        b.equivFun.symm.toLinearMap)
    have hw : Function.Injective (A (b.equivFun L)) := by
      simpa only [A,LinearEquiv.symm_apply_apply] using hL
    obtain ⟨D,hD,hgood⟩ := injective_polynomial_principal_open A hA (b.equivFun L) hw
    exact ⟨D,⟨b.equivFun L,hD⟩,hgood⟩
  choose D hD hgood using hlocal
  have hne (i : I) : D i ≠ 0 := by
    obtain ⟨x,hx⟩ := hD i
    intro hz
    simp [hz] at hx
  obtain ⟨x,hx⟩ := nonempty_principal_intersection D hne
  refine ⟨∏ i, D i,⟨x,?_⟩,?_⟩
  · simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr (fun i _ => hx i)
  intro x hx i
  have hh : ∏ i, eval x (D i) ≠ 0 := by simpa only [map_prod] using hx
  exact hgood i x (Finset.prod_ne_zero_iff.mp hh i (Finset.mem_univ _))

theorem exists_finite_subspace_projection (U : I → Submodule K V)
    (hU : ∀ i, finrank K (U i) ≤ finrank K W) :
    ∃ L : V →ₗ[K] W, ∀ i, Function.Injective (L.comp (U i).subtype) := by
  obtain ⟨D,⟨x,hx⟩,hgood⟩ := finite_subspace_projection_open U hU
  exact ⟨(Module.finBasis K (V →ₗ[K] W)).equivFun.symm x,hgood x hx⟩

end Froberg
