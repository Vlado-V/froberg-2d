module

public import Froberg.ThinScalarOpen
public import Froberg.ScalarQuotientSlices
public import Froberg.ActualClosedKernelSlices
public import Froberg.StrictVectorModel

@[expose] public section

/-! The thin-case conclusion on the actual scalar quotient, with literal
homogeneous closed equations and exactly the prescribed number of slices. -/
noncomputable section
namespace Froberg.BilinearScalarFamily
open Module MvPolynomial Quartic PolynomialBilinearCoordinates
variable {K F V W : Type*} [Field K] [Infinite K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {q j : ℕ}

def HasThinQuotientOpen (mu : F →ₗ[K] V →ₗ[K] W) (q j : ℕ) (C : ℝ) : Prop :=
  ∃ P : MvPolynomial (Fin q × Fin (finrank K F)) K,
    (∃ Q : Fin q → F,eval (fun ik => coordinates K F (Q ik.1) ik.2) P ≠ 0) ∧
    ∀ Q : Fin q → F,eval (fun ik => coordinates K F (Q ik.1) ik.2) P ≠ 0 →
      Function.Injective (multiplication mu Q) ∧
      finrank K (ScalarQuotient mu Q)=j ∧
      HasClosedKernelSlices (scalarQuotientBilinear mu Q) (BilinearCovectorStrata.thinSlices j C)

theorem principal_open_thin_quotient_strata (mu : F →ₗ[K] V →ₗ[K] W)
    (ha : 0 < finrank K V) (hT : finrank K W=q*finrank K V+j)
    (G C : ℝ) (hC : 0 ≤ C) (hG₁ : (finrank K V : ℝ)+C ≤ G)
    (hG₂ : (finrank K V : ℝ)+(j : ℝ)/finrank K V ≤ G)
    (hgrowth : ∀ U : Submodule K V,
      ((finrank K W : ℝ)/finrank K V)*finrank K U+
        G*(min (finrank K U) (finrank K V-finrank K U) : ℕ) ≤
        finrank K (BilinearImage.image mu U)) :
    ∃ P : MvPolynomial (Fin q × Fin (finrank K F)) K,
      (∃ Q : Fin q → F,eval (fun ik => coordinates K F (Q ik.1) ik.2) P ≠ 0) ∧
      ∀ Q : Fin q → F,eval (fun ik => coordinates K F (Q ik.1) ik.2) P ≠ 0 →
        Function.Injective (multiplication mu Q) ∧
        finrank K (ScalarQuotient mu Q)=j ∧
        HasClosedKernelSlices (scalarQuotientBilinear mu Q) (BilinearCovectorStrata.thinSlices j C) := by
  obtain ⟨P,Z,hP,hgood⟩ := principal_open_thin_injective mu ha hT G C hC hG₁ hG₂ hgrowth
  refine ⟨P,hP,?_⟩
  intro Q hQ
  obtain ⟨hi,hZ⟩ := hgood Q hQ
  refine ⟨hi,?_,?_⟩
  · change finrank K (W ⧸ (multiplication mu Q).range)=j
    rw [quotient_finrank mu Q hi,hT]
    omega
  · exact exists_actual_closed_kernel_slices (scalarQuotientBilinear mu Q)
      (BilinearCovectorStrata.thinSlices j C)
      (fun r t => (multiplication mu Q).range.mkQ (Z r t))
      (transport_scalar_quotient_slices mu Q _ Z hZ)

end Froberg.BilinearScalarFamily

namespace Froberg.VectorExpansionOpen
open Module MvPolynomial Quartic PolynomialBilinearCoordinates VectorMultiplicationCoordinates
open BilinearScalarFamily
variable {K : Type*} [Field K] [Infinite K] {h n s d c q j : ℕ} {G C : ℝ}

theorem StrictModel.generic_thin_quotient_strata {g : Fin c → Rows K h n s}
    (hg : StrictModel g d G) (hT : finrank K (Target g d)=q*finrank K (Source g)+j)
    (hC : 0 ≤ C) (hG₁ : (finrank K (Source g) : ℝ)+C ≤ G)
    (hG₂ : (finrank K (Source g) : ℝ)+(j : ℝ)/finrank K (Source g) ≤ G) :
    ∃ P : MvPolynomial (Fin q × Fin (finrank K (Forms K n d))) K,
      (∃ Q : Fin q → Forms K n d,eval (fun ik => coordinates K _ (Q ik.1) ik.2) P ≠ 0) ∧
      ∀ Q : Fin q → Forms K n d,eval (fun ik => coordinates K _ (Q ik.1) ik.2) P ≠ 0 →
        Function.Injective (BilinearScalarFamily.multiplication (quotientMultiplication g d) Q) ∧
        finrank K (ScalarQuotient (quotientMultiplication g d) Q)=j ∧
        HasClosedKernelSlices (scalarQuotientBilinear (quotientMultiplication g d) Q)
          (BilinearCovectorStrata.thinSlices j C) :=
  principal_open_thin_quotient_strata (quotientMultiplication g d)
    hg.source_pos hT G C hC hG₁ hG₂ hg.growth

end Froberg.VectorExpansionOpen
