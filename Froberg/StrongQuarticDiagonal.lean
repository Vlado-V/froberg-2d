module

public import Froberg.PreparedBiformCoordinates
public import Froberg.SpecialDiagonalBiform
public import Froberg.PairedScalarSeparation

@[expose] public section

/-! The literal quartic block space supplies the exceptional diagonal
capacity used in degrees five through eight. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]

theorem strong_quartic_diagonal_exists {h n m : ℕ} (hh : 144≤h) (hfour : 4∣h)
    (C : Submodule K (Poly K n)) [Module.Finite K C]
    (hC : Function.Injective (subspaceSymmetricMultiplication C))
    (hm : m≤(h^4/256)*(finrank K C/2)) :
    ∃ f : Fin m → MvPolynomial (Fin h ⊕ Fin n) K,
      (∀ i,f i∈biformImage (Forms K h 4) C) ∧ LinearIndependent K (pairProducts f) := by
  obtain ⟨O,hO,hOd,hOi⟩ := QuarticBlocks.quartic_space_exists (K := K) hh hfour
  letI : Module.Finite K O := Submodule.finiteDimensional_of_le hO
  obtain ⟨f,hf,hfi⟩ := exists_diagonal_sum_biforms O C hOi hC (by simpa only [hOd] using hm)
  exact ⟨f,fun i => biformImage_mono hO le_rfl (hf i),hfi⟩

theorem strong_quartic_linear_diagonal_exists {h n m : ℕ} (hh : 144≤h) (hfour : 4∣h)
    (hm : m≤(h^4/256)*(n/2)) :
    ∃ f : Fin m → MvPolynomial (Fin h ⊕ Fin n) K,
      (∀ i,f i∈biformImage (Forms K h 4) (Forms K n 1)) ∧
      LinearIndependent K (pairProducts f) := by
  obtain ⟨C,hC,hCd,hCi⟩ := linear_scalar_space_exists (K := K) n
  letI : Module.Finite K C := Submodule.finiteDimensional_of_le hC
  obtain ⟨f,hf,hfi⟩ := strong_quartic_diagonal_exists hh hfour C hCi (by simpa only [hCd] using hm)
  exact ⟨f,fun i => biformImage_mono le_rfl hC (hf i),hfi⟩

theorem strong_quartic_paired_diagonal_exists {h n m t : ℕ} (hh : 144≤h) (hfour : 4∣h)
    (S : Finset (Fin n)) (hS : S.card≤Sᶜ.card)
    (hm : m≤(h^4/256)*(S.card.choose t/2)) :
    ∃ (C : Submodule K (Poly K n)) (f : Fin m → MvPolynomial (Fin h ⊕ Fin n) K),
      C≤Forms K n t ∧ C*C≤deletedBidegreeSpace K S (2*t) (2*(t/2)) ∧
      (∀ i,f i∈biformImage (Forms K h 4) C) ∧ LinearIndependent K (pairProducts f) := by
  obtain ⟨C,hC,hCd,hCi,hprofile⟩ := paired_scalar_space_exists (K := K) S hS t
  letI : Module.Finite K C := Submodule.finiteDimensional_of_le hC
  obtain ⟨f,hf,hfi⟩ := strong_quartic_diagonal_exists hh hfour C hCi (by simpa only [hCd] using hm)
  exact ⟨C,f,hC,hprofile,hf,hfi⟩

end Froberg
