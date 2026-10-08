import Froberg.QuadraticExtendedRow
import Froberg.PreparedFiniteRows
import Froberg.FiniteEvenProjectedRow
import Froberg.ZeroPreparedExtendedWitness

noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial AttachedMultiplication
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem exists_higher_extended_row_parameter {w v z d q b : ℕ}
    {J : Finset ℕ} {counts : ℕ → ℕ}
    {T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X}
    (R : J) (h : HigherRowCapacity w v d q b J counts T R)
    (ell : Fin 2 → Forms K (v+v) 1) (hell : LinearIndependent K ell) :
    let hO : ∀ j∈J,constrainedOutputs T j≤homogeneousSubmodule (Fin w × Bool) K j :=
      fun _ _ => inf_le_left
    ∃ p : Space (v+v+z) d q J counts (constrainedOutputs T),
      LinearIndependent K (fun i => intrinsicLayerMap hO R i p) ∧
      (row hO R p).ker=(rowConstants hO R p).range := by
  classical
  dsimp only
  letI : Module.Finite K (homogeneousSubmodule (Fin w × Bool) K R.val) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg _ _ _)
  let bo := Module.finBasis K (homogeneousSubmodule (Fin w × Bool) K R.val)
  obtain ⟨e,zv,he,Q,E,hproj,hER,hRdeg,hrest,hfull,hker⟩ :=
    exists_finite_even_projected_row h.hw h.hv bo
      (fun _ : Fin 0 => (⊥ : Submodule K (Fin (finrank K (homogeneousSubmodule (Fin w × Bool) K R.val)) → K)))
      (fun i => Fin.elim0 i) counts J
      h.positive h.even h.degree T h.diagonal h.cross h.output_positive
      h.enough_generators h.divisor_capacity h.incidence h.scalar_open
  let o := fun j => (bo j).val
  have ho : LinearIndependent K o := bo.linearIndependent.map'
    (homogeneousSubmodule (Fin w × Bool) K R.val).subtype (Submodule.ker_subtype _)
  have hmem : ∀ j∈J,∀ i,E j i∈biformImage (constrainedOutputs T j) (Forms K (v+v) (d-j)) := by
    intro j hj i
    by_cases hjR : j=R.val
    · subst j
      rw [hER i,constrainedOutputs,h.new_unconstrained,LinearMap.ker_zero,inf_top_eq]
      rw [←polynomialFormVector_attachedCoordinates o e zv he i]
      exact polynomialFormVector_mem_biform o _ _ (fun j => (bo j).property) _
        (fun a => (attachedCoordinates e zv he i a).property)
    · apply mem_biformImage_inf_kernel
      · apply mem_biformImage_of_homogeneous
        · simpa only [Nat.add_sub_of_le (h.degree j hj)] using (hrest j hjR i).1
        · exact (hrest j hjR i).2.1
      · exact (hrest j hjR i).2.2
  let p₀ := ofPolynomialFamilies (Q ∘ Fintype.equivFin (Label q J counts)) E hmem
  let p := coreExtension z p₀
  have hp : LinearIndependent K (fun i => intrinsicLayerMap (fun j _ =>
      (inf_le_left : constrainedOutputs T j ≤ homogeneousSubmodule (Fin w × Bool) K j)) R i p) ∧
      (row (fun j _ => inf_le_left) R p).ker=(rowConstants (fun j _ => inf_le_left) R p).range := by
    by_cases hlt : R.val<d
    · exact sparse_core_extended_parameter_exact (z := z) (fun j _ => inf_le_left)
        h.degree R hlt o ho (fun j => (bo j).property) e zv he Q E hmem hER hfull hker ell hell
    · exact sparse_core_extended_parameter_exact_zero (z := z) (fun j _ => inf_le_left)
        h.degree R (by have := h.degree R.val R.property; omega)
        o ho (fun j => (bo j).property) e zv he Q E hmem hER hfull hker ell hell
  exact ⟨p,hp⟩

end Froberg.PreparedParameters
