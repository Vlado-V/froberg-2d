module

public import Froberg.PreparedPrivateQuadraticWitness
public import Froberg.PreparedExtendedWitness

@[expose] public section

/-! The same finite row capacities give literal witnesses after adjoining
any fixed number of scalar variables, including the scalar-degree-zero row. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial AttachedMultiplication
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem exists_quadratic_extended_row_parameter {σ : Type*} [Fintype σ]
    {a z d q b : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    {O : ℕ → Submodule K (MvPolynomial σ K)}
    (hd : 3≤d) (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,2≤j) (hJd : ∀ j∈J,j≤d) (h2 : 2∈J)
    (cap : QuadraticRowCapacity a d q b J counts O)
    (ell : Fin 2 → Forms K a 1) (hell : LinearIndependent K ell) :
    ∃ p : Space (a+z) d q J counts O,
      LinearIndependent K (fun i => intrinsicLayerMap hO ⟨2,h2⟩ i p) ∧
      (row hO ⟨2,h2⟩ p).ker=(rowConstants hO ⟨2,h2⟩ p).range := by
  classical
  obtain ⟨o,e,v,he,Q,ho,hdeg,hmem,hhom,hzero,hall,hrow⟩ :=
    exists_sparse_full_output_row_all_degrees cap.variables_positive (O 2) (hO 2 h2)
      cap.output_positive cap.enough_generators cap.divisor_capacity cap.incidence cap.scalar_open
  let E : (j : ℕ) → Fin (counts j) → MvPolynomial (σ ⊕ Fin a) K :=
    Function.update (fun _ _ => 0) 2 (attachedPolynomialFamily o e v)
  have hER : ∀ i,E 2 i=attachedPolynomialFamily o e v i := by simp [E]
  have hEmem : ∀ j∈J,∀ i,E j i∈biformImage (O j) (Forms K a (d-j)) := by
    intro j hj i
    by_cases heq : j=2
    · subst j
      rw [hER]
      exact hmem i
    · rw [show E j i=0 by simp [E,heq]]
      exact Submodule.zero_mem _
  letI : IsEmpty (ProductRows.Row J 2) := ProductRows.first_even_row_empty hJ
  have hrow' := addRow_exact_of_subsingleton (polynomialIntermediateRow o e v he Q)
    (ProductRows.multiplication counts E J 2) (intermediateKoszul e v he Q) hrow
  let p₀ := ofPolynomialFamilies (Q ∘ Fintype.equivFin (Label q J counts)) E hEmem
  let p := coreExtension z p₀
  have hp := sparse_core_extended_parameter_exact (z := z) hO hJd ⟨2,h2⟩ (by change 2<d; omega)
    o ho hdeg e v he Q E hEmem hER hall hrow' ell hell
  exact ⟨p,hp⟩

end Froberg.PreparedParameters
