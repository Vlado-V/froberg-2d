import Froberg.PreparedWitnessEmbedding
import Froberg.SparseFullOutput
import Froberg.EmptyProductRow

/-! The quadratic new-layer witness is constructed in its prescribed output
space D; the first even row has no formal product block. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial AttachedMultiplication Quartic.PolynomialBilinearCoordinates
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ]

structure QuadraticRowCapacity (n d q b : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
    (O : ℕ → Submodule K (MvPolynomial σ K)) : Prop where
  variables_positive : 0<n
  output_positive : 0<finrank K (O 2)
  enough_generators : counts 2≤b*(n+(d-2)-1).choose (d-2)
  divisor_capacity : b*((d-2)+d).choose (d-2)≤finrank K (O 2)
  incidence : finrank K (O 2)*((d-2)+d).choose (d-2) *
    (Fintype.card (Label q J counts)+finrank K (O 2)*(n+(d-2)-1).choose (d-2)+
      (finrank K (O 2)*2^(finrank K (O 2)))*(n+(d-1)-1).choose (d-1)) ≤
    (finrank K (O 2)-b*((d-2)+d).choose (d-2))*(n+(d-2)+d-1).choose d
  scalar_open : ∃ D : MvPolynomial
      (Fin (finrank K (Fin (Fintype.card (Label q J counts)) → Forms K n d))) K,
    (∃ Q : Fin (Fintype.card (Label q J counts)) → Forms K n d,
      eval (coordinates K _ Q) D≠0) ∧
    ∀ Q : Fin (Fintype.card (Label q J counts)) → Forms K n d,
      eval (coordinates K _ Q) D≠0 → Function.Injective (prefixMultiplication Q (d-2))

/-- A concrete quadratic sparse witness lies in the same full coefficient
space used for every higher even row. -/
theorem exists_quadratic_row_parameter {n d q b : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    {O : ℕ → Submodule K (MvPolynomial σ K)}
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,2≤j) (h2 : 2∈J)
    (h : QuadraticRowCapacity n d q b J counts O) :
    ∃ p : Space n d q J counts O,
      LinearIndependent K (fun i => intrinsicLayerMap hO ⟨2,h2⟩ i p) ∧
      (row hO ⟨2,h2⟩ p).ker=(rowConstants hO ⟨2,h2⟩ p).range := by
  classical
  obtain ⟨o,e,z,he,Q,ho,hdeg,hmem,hhom,hzero,hker⟩ :=
    exists_sparse_full_output_row h.variables_positive (O 2) (hO 2 h2)
      h.output_positive h.enough_generators h.divisor_capacity h.incidence h.scalar_open
  let E : (j : ℕ) → Fin (counts j) → MvPolynomial (σ ⊕ Fin n) K :=
    Function.update (fun _ _ => 0) 2 (attachedPolynomialFamily o e z)
  have hER : ∀ i,E 2 i=attachedPolynomialFamily o e z i := by simp [E]
  have hEmem : ∀ j∈J,∀ i,E j i∈biformImage (O j) (Forms K n (d-j)) := by
    intro j hj i
    by_cases heq : j=2
    · subst j
      rw [hER]
      exact hmem i
    · rw [show E j i=0 by simp [E,heq]]
      exact Submodule.zero_mem _
  letI : IsEmpty (ProductRows.Row J 2) := ProductRows.first_even_row_empty hJ
  have hfull := addRow_exact_of_subsingleton (polynomialIntermediateRow o e z he Q)
    (ProductRows.multiplication counts E J 2) (intermediateKoszul e z he Q) hker
  exact sparse_witness_common_parameter hO ⟨2,h2⟩ o ho hdeg e z he Q E hEmem hER hzero hfull

end Froberg.PreparedParameters
