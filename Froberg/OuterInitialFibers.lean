import Froberg.OuterInitial
import Froberg.SeparatedSubspace

/-! Initial outer-module subspaces indexed by the actual monomials. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open Module Quartic.HomogeneousCoefficientCoordinates
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I] {n s d h : ℕ}
variable (e : I → Fin n →₀ ℕ) (v : I → Fin h → K) (he : ∀ i, (e i).degree = s)

def initialMonomialFibers
    (L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he))
    (a : Exponent n s) : Submodule K ((Fin h → K) ⧸ relationFiber e v a.val) :=
  coordinateSubmodule ((outerInitial e v he L).map (quotientFiberEquiv (d := 0) e v he).toLinearMap) a

theorem map_initial_monomial_fibers
    (L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)) :
    (outerInitial e v he L).map (quotientFiberEquiv (d := 0) e v he).toLinearMap =
      Submodule.pi Set.univ (initialMonomialFibers e v he L) := by
  apply eq_pi_of_reindex_eq_pi (OrderedMonomials.enumerate n s) _ (initialFibers e v he L)
  rw [← Submodule.map_comp]
  exact map_outerInitial e v he L

theorem sum_initialMonomialFibers_finrank
    (L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)) :
    (∑ a, finrank K (initialMonomialFibers e v he L a)) = finrank K L := by
  have hh := (quotientFiberEquiv (d := 0) e v he).finrank_map_eq (outerInitial e v he L)
  rw [map_initial_monomial_fibers,finrank_coordinate_pi] at hh
  exact hh.trans (outerInitial_finrank e v he L)

/-- The actual polynomial image and its monomial quotient-fiber image agree. -/
theorem map_outerImage_fibers
    (L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)) :
    (outerImage (d := d) e v he L).map (quotientFiberEquiv e v he).toLinearMap =
      Quartic.BilinearImage.image (fiberMultiply (d := d) e v he)
        (L.map (quotientFiberEquiv (d := 0) e v he).toLinearMap) := by
  rw [outerImage,Quartic.BilinearImage.image,Quartic.BilinearImage.image,Submodule.map_iSup]
  congr 1
  funext f
  rw [← Submodule.map_comp,← Submodule.map_comp]
  congr 1
  ext x
  simp [fiberMultiply]

/-- The independent actual monomial fibers of every source subspace have the
same total dimension and a no-larger genuine multiplication image. -/
theorem initial_monomial_image_finrank_le
    (L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)) :
    finrank K (Quartic.BilinearImage.image (fiberMultiply (d := d) e v he)
      (Submodule.pi Set.univ (initialMonomialFibers e v he L))) ≤
      finrank K (outerImage (d := d) e v he L) := by
  rw [← map_initial_monomial_fibers,← map_outerImage_fibers,
    (quotientFiberEquiv (d := d) e v he).finrank_map_eq]
  exact outerImage_initial_finrank_le e v he L

/-- A convenient complete initial-replacement interface for the uniform growth proof. -/
theorem exists_initial_monomial_fibers
    (L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)) :
    ∃ C : (a : Exponent n s) → Submodule K ((Fin h → K) ⧸ relationFiber e v a.val),
      (∑ a, finrank K (C a)) = finrank K L ∧
      finrank K (Quartic.BilinearImage.image (fiberMultiply (d := d) e v he)
        (Submodule.pi Set.univ C)) ≤ finrank K (outerImage (d := d) e v he L) :=
  ⟨initialMonomialFibers e v he L,sum_initialMonomialFibers_finrank e v he L,
    initial_monomial_image_finrank_le e v he L⟩

end Froberg.AttachedMultiplication
