module

public import Froberg.PreparedFourthRow
public import Froberg.PreparedExtendedWitness
public import Froberg.PreparedPrivateSeparation
public import Froberg.FiniteFourthProjectedRow

@[expose] public section

/-! A finite higher-row capacity constructs a successful augmented row for
the same prescribed private tuple. Its coefficients belong to the actual
common prepared space, including the adjoined private scalar variables. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial PrivateColumns AttachedMultiplication
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem exists_fourth_private_row_parameter {w v z d q b t : ℕ}
    {J : Finset ℕ} {counts : ℕ → ℕ}
    {T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X}
    (hRJ : 4∈J) (hd : 3≤d) (hRd : 4<d)
    (h : FourthRowCapacity w v d q b J counts T)
    (bi : Basis (Fin (finrank K (homogeneousSubmodule (Fin w × Bool) K 3)))
      K (homogeneousSubmodule (Fin w × Bool) K 3))
    (bo : Basis (Fin (finrank K (homogeneousSubmodule (Fin w × Bool) K 4)))
      K (homogeneousSubmodule (Fin w × Bool) K 4))
    (l : Fin t → homogeneousSubmodule (Fin w × Bool) K 1) (hl : ∀ i,l i≠0)
    (ι : Fin t ↪ Fin z)
    (hrelations : ∀ i,b*((d-4)+1).choose (d-4)≤oddOutputDimension w 4-
      finrank K (privateOutputMatrix bi bo (l i)).range)
    (ell : Fin 2 → Forms K (v+v) 1) (hell : LinearIndependent K ell) :
    let r : J := ⟨4,hRJ⟩
    let hO : ∀ j∈J,constrainedOutputs T j≤homogeneousSubmodule (Fin w × Bool) K j := fun _ _ => inf_le_left
    let P : Fin t → MvPolynomial ((Fin w × Bool) ⊕ Fin (v+v+z)) K := fun i => rename Sum.inl (l i).val*
      rename Sum.inr (monomial (privateExponent (v+v) (d-1) ι i) (1:K))
    ∃ p : Space (v+v+z) d q J counts (constrainedOutputs T),
      (privateAugmentedRow hO r p P).ker=(privateAugmentedConstants (b := t) hO r p).range := by
  classical
  obtain ⟨e,zv,he,Q,E,hproj,hER,hRdeg,hrest,hfull,hker⟩ :=
    exists_finite_fourth_projected_row h.hw h.hv bo
      (fun i => (privateOutputMatrix bi bo (l i)).range) hrelations counts J
      (fun j hj => by have := h.low j hj; omega) h.even h.degree T h.low h.diagonal h.output_positive
      h.enough_generators h.divisor_capacity h.incidence h.scalar_open
  let o := fun j => (bo j).val
  have ho : LinearIndependent K o := bo.linearIndependent.map'
    (homogeneousSubmodule (Fin w × Bool) K 4).subtype (Submodule.ker_subtype _)
  have hmem : ∀ j∈J,∀ i,E j i∈biformImage (constrainedOutputs T j) (Forms K (v+v) (d-j)) := by
    intro j hj i
    by_cases hjR : j=4
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
  have hp := sparse_core_extended_parameter_exact (z := z) (fun j _ => (inf_le_left : constrainedOutputs T j ≤ homogeneousSubmodule (Fin w × Bool) K j))
    h.degree (⟨4,hRJ⟩ : J) hRd o ho (fun j => (bo j).property) e zv he Q E hmem hER hfull hker ell hell
  refine ⟨p,?_⟩
  apply private_augmented_exact (fun j _ => (inf_le_left : constrainedOutputs T j ≤ homogeneousSubmodule (Fin w × Bool) K j)) (⟨4,hRJ⟩ : J) p _ hp.2
  exact private_core_row_separation hd (by omega : 2≤3) (by omega) hRJ
    (fun j _ => (inf_le_left : constrainedOutputs T j ≤ homogeneousSubmodule (Fin w × Bool) K j)) h.degree bi bo l hl ι e zv hproj p₀ (by
      intro i
      simpa only [p₀,layers_ofPolynomialFamilies _ _ _ hRJ] using hER i)

end Froberg.PreparedParameters
