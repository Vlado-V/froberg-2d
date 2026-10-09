module

public import Froberg.PairedSpace
public import Froberg.SeparatedCoefficientSpaces
public import Froberg.SubspaceProductRestriction

@[expose] public section

/-! The diagonal-pair construction in Lemma B.4, including the loss from
any finite-dimensional output constraint. -/
noncomputable section
namespace Froberg
open Module TensorProduct PairedMonomials
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

/-- Paired output and scalar spaces yield every diagonal source size below
the exact finite-variable capacity. The output constraint is arbitrary. -/
theorem paired_diagonal_space_exists (w v j t m : ℕ)
    (T : MvPolynomial (Fin w × Bool) K →ₗ[K] X)
    (hm : m ≤ (w.choose j - finrank K X) * (v.choose t / 2)) :
    ∃ (O : Submodule K (MvPolynomial (Fin w × Bool) K))
      (C : Submodule K (MvPolynomial (Fin v × Bool) K))
      (E : Submodule K (MvPolynomial (Fin w × Bool) K ⊗[K]
        MvPolynomial (Fin v × Bool) K)),
      O ≤ MvPolynomial.homogeneousSubmodule (Fin w × Bool) K j ∧
      O ≤ MvPolynomial.weightedHomogeneousSubmodule K pairedWeight (j/2,j-j/2) ∧
      O ≤ T.ker ∧
      C ≤ MvPolynomial.homogeneousSubmodule (Fin v × Bool) K t ∧
      C ≤ MvPolynomial.weightedHomogeneousSubmodule K pairedWeight (t/2,t-t/2) ∧
      E ≤ LinearMap.range (TensorProduct.map O.subtype C.subtype) ∧
      finrank K E = m ∧ Function.Injective (subspaceSymmetricMultiplication E) := by
  obtain ⟨O₀,hOh,hOb,hOd,hOi⟩ := paired_space_exists (K := K) w j
  obtain ⟨C,hCh,hCb,hCd,hCi⟩ := paired_space_exists (K := K) v t
  letI : Module.Finite K (MvPolynomial.homogeneousSubmodule (Fin w × Bool) K j) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg _ _ _)
  letI : Module.Finite K (MvPolynomial.homogeneousSubmodule (Fin v × Bool) K t) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg _ _ _)
  letI : Module.Finite K O₀ := Submodule.finiteDimensional_of_le hOh
  letI : Module.Finite K C := Submodule.finiteDimensional_of_le hCh
  let O := O₀ ⊓ T.ker
  letI : Module.Finite K O := Submodule.finiteDimensional_of_le (show O ≤ O₀ from inf_le_left)
  have hO : w.choose j - finrank K X ≤ finrank K O := by
    simpa only [hOd] using finrank_intersection_kernel_lower_bound O₀ T
  have hOi' : Function.Injective (subspaceSymmetricMultiplication O) :=
    subspaceSymmetricMultiplication_injective_mono inf_le_left hOi
  have hm' : m ≤ finrank K O * (finrank K C / 2) := by
    rw [hCd]
    exact hm.trans (Nat.mul_le_mul_right _ hO)
  obtain ⟨E,hE,hEd,hEi⟩ := separated_coefficient_space_exists O C hOi' hCi hm'
  exact ⟨O,C,E,inf_le_left.trans hOh,inf_le_left.trans hOb,inf_le_right,
    hCh,hCb,hE,hEd,hEi⟩

end Froberg
