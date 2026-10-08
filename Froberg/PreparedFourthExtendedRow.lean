import Froberg.PreparedFourthRow
import Froberg.PreparedExtendedWitness

/-! The small-degree fourth-row witness remains exact after adjoining any
fixed number of scalar variables. -/
noncomputable section
set_option maxHeartbeats 2200000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial AttachedMultiplication
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem exists_fourth_extended_row_parameter {w v z d q b : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    {T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X} (h4 : 4∈J)
    (h : FourthRowCapacity w v d q b J counts T) (hd : 4<d)
    (ell : Fin 2 → Forms K (v+v) 1) (hell : LinearIndependent K ell) :
    ∃ p : Space (v+v+z) d q J counts (constrainedOutputs T),
      LinearIndependent K (fun i => intrinsicLayerMap (fun _ _ => inf_le_left) ⟨4,h4⟩ i p) ∧
      (row (fun _ _ => inf_le_left) ⟨4,h4⟩ p).ker=
        (rowConstants (fun _ _ => inf_le_left) ⟨4,h4⟩ p).range := by
  obtain ⟨o,e,zv,he,Q,E,ho,hdeg,hER,hRdeg,hrest,hzero,hker⟩ :=
    exists_finite_fourth_row h.hw h.hv counts J (fun j hj => by have := h.low j hj; omega) h.even h.degree T
      h.low h.diagonal h.output_positive h.enough_generators h.divisor_capacity h.incidence h.scalar_open
  have hmem : ∀ j∈J,∀ i,E j i∈biformImage (constrainedOutputs T j) (Forms K (v+v) (d-j)) := by
    intro j hj i
    by_cases hjR : j=4
    · subst j
      rw [hER i,constrainedOutputs,h.new_unconstrained,LinearMap.ker_zero,inf_top_eq]
      rw [← polynomialFormVector_attachedCoordinates o e zv he i]
      exact polynomialFormVector_mem_biform o _ _ hdeg _ (fun a => (attachedCoordinates e zv he i a).property)
    · apply mem_biformImage_inf_kernel
      · apply mem_biformImage_of_homogeneous
        · simpa only [Nat.add_sub_of_le (h.degree j hj)] using (hrest j hjR i).1
        · exact (hrest j hjR i).2.1
      · exact (hrest j hjR i).2.2
  let p₀ := ofPolynomialFamilies (Q ∘ Fintype.equivFin (Label q J counts)) E hmem
  refine ⟨coreExtension z p₀,?_⟩
  exact sparse_core_extended_parameter_exact (z := z) (fun _ _ => inf_le_left) h.degree
    ⟨4,h4⟩ hd o ho hdeg e zv he Q E hmem hER hzero hker ell hell


end Froberg.PreparedParameters
