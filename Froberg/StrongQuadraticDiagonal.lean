import Froberg.SpecialDiagonalBiform
import Froberg.PreparedBiformCoordinates
import Froberg.PairedScalarSeparation

/-! The full quadratic block space can be used before imposing the output
detector. Its larger dimension supplies the small-degree diagonal witnesses. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem strong_quadratic_space_exists (h : ℕ) :
    ∃ O : Submodule K (Poly K h),O≤Forms K h 2 ∧
      finrank K O=2*(h/2).choose 2 ∧
      Function.Injective (subspaceSymmetricMultiplication O) := by
  obtain ⟨q,hq,hprod⟩ := QuadraticBlocks.exists_independent_quadrics (K := K)
    (h := h) (w := h/2) (m := 2*(h/2).choose 2) (by omega) le_rfl
  refine ⟨Submodule.span K (Set.range q),?_,?_,?_⟩
  · exact Submodule.span_le.mpr (by rintro p ⟨i,rfl⟩; exact hq i)
  · rw [finrank_span_eq_card (linearIndependent_of_pairProducts q hprod),Fintype.card_fin]
  · exact symmetricMultiplication_injective_of_pairProducts q hprod

theorem strong_quadratic_diagonal_exists {h n m : ℕ}
    (C : Submodule K (Poly K n)) [Module.Finite K C]
    (hC : Function.Injective (subspaceSymmetricMultiplication C))
    (T : Poly K h →ₗ[K] X)
    (hm : m≤(2*(h/2).choose 2-finrank K X)*(finrank K C/2)) :
    ∃ f : Fin m → MvPolynomial (Fin h ⊕ Fin n) K,
      (∀ i,f i∈biformImage (Forms K h 2⊓T.ker) C) ∧
      LinearIndependent K (pairProducts f) := by
  obtain ⟨O,hO,hOd,hOi⟩ := strong_quadratic_space_exists (K := K) h
  letI : Module.Finite K O := Submodule.finiteDimensional_of_le hO
  obtain ⟨f,hf,hfi⟩ := exists_constrained_diagonal_biforms O C hOi hC T
    (by simpa only [hOd] using hm)
  exact ⟨f,fun i => biformImage_mono (inf_le_inf_right T.ker hO) le_rfl (hf i),hfi⟩

theorem strong_quadratic_linear_diagonal_exists {h n m : ℕ}
    (T : Poly K h →ₗ[K] X)
    (hm : m≤(2*(h/2).choose 2-finrank K X)*(n/2)) :
    ∃ f : Fin m → MvPolynomial (Fin h ⊕ Fin n) K,
      (∀ i,f i∈biformImage (Forms K h 2⊓T.ker) (Forms K n 1)) ∧
      LinearIndependent K (pairProducts f) := by
  obtain ⟨C,hC,hCd,hCi⟩ := linear_scalar_space_exists (K := K) n
  letI : Module.Finite K C := Submodule.finiteDimensional_of_le hC
  obtain ⟨f,hf,hfi⟩ := strong_quadratic_diagonal_exists C hCi T
    (by simpa only [hCd] using hm)
  exact ⟨f,fun i => biformImage_mono le_rfl hC (hf i),hfi⟩

theorem strong_quadratic_paired_diagonal_exists {h n m t : ℕ}
    (T : Poly K h →ₗ[K] X) (S : Finset (Fin n)) (hS : S.card≤Sᶜ.card)
    (hm : m≤(2*(h/2).choose 2-finrank K X)*(S.card.choose t/2)) :
    ∃ (C : Submodule K (Poly K n)) (f : Fin m → MvPolynomial (Fin h ⊕ Fin n) K),
      C≤Forms K n t ∧ C*C≤deletedBidegreeSpace K S (2*t) (2*(t/2)) ∧
      (∀ i,f i∈biformImage (Forms K h 2⊓T.ker) C) ∧
      LinearIndependent K (pairProducts f) := by
  obtain ⟨C,hC,hCd,hCi,hprofile⟩ := paired_scalar_space_exists (K := K) S hS t
  letI : Module.Finite K C := Submodule.finiteDimensional_of_le hC
  obtain ⟨f,hf,hfi⟩ := strong_quadratic_diagonal_exists C hCi T
    (by simpa only [hCd] using hm)
  exact ⟨C,f,hC,hprofile,hf,hfi⟩

end Froberg
