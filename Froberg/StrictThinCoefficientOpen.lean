module

public import Froberg.CountedJointSelection

@[expose] public section

/-! A common finite input for the prepared and restored C.4 selectors. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial VectorExpansionOpen BilinearScalarFamily

/-- A full outer-coefficient open carrying the strict model and thin quotient. -/
def StrictThinCoefficientOpen (K : Type) [Field K] (h n d f : ℕ) (G C : ℝ) : Prop :=
  ∃ D : MvPolynomial (VectorParameters.Index h n (d-1) f) K,
    (∃ p, eval p D ≠ 0) ∧ ∀ p, eval p D ≠ 0 →
      StrictModel (VectorParameters.generators p) d G ∧
      HasThinQuotientOpen (quotientMultiplication (VectorParameters.generators p) d)
        (upperCount n d) (outerScalarDeficit (VectorParameters.generators p)) C

theorem strictThinCoefficientOpen_joint {K : Type} [Field K] [Infinite K]
    {h n d f : ℕ} {G C : ℝ} (hnpos : 0 < n)
    (houter : StrictThinCoefficientOpen K h n d f G C) :
    ∀ (I : Type*)
      (P : MvPolynomial (VectorParameters.Index h n (d-1) f ⊕
        (CoefficientIndex n d (upperCount n d) ⊕ I)) K),
      (∃ p,eval p P ≠ 0) →
      ∃ pF pQ pI,eval (Sum.elim pF (Sum.elim pQ pI)) P ≠ 0 ∧
        StrictModel (VectorParameters.generators pF) d G ∧
        ChildFlagCondition (quotientMultiplication (VectorParameters.generators pF) d)
          (outerScalarDeficit (VectorParameters.generators pF)) C pQ := by
  intro I P hP
  obtain ⟨D,hD,hmodel⟩ := houter
  let Phi := fun (pF : VectorParameters.Index h n (d-1) f → K)
    (pQ : CoefficientIndex n d (upperCount n d) → K) => ChildFlagCondition
    (quotientMultiplication (VectorParameters.generators pF) d)
      (outerScalarDeficit (VectorParameters.generators pF)) C pQ
  have hfiber : ∀ pF,eval pF D ≠ 0 → ∃ Q : MvPolynomial (CoefficientIndex n d (upperCount n d)) K,
      (∃ pQ,eval pQ Q ≠ 0) ∧ ∀ pQ,eval pQ Q ≠ 0 → Phi pF pQ := by
    intro pF hpF
    exact thin_generic_flag_principal_open _ hnpos (Nat.sub_le _ 1)
      (upperCount_le_monomial_count hnpos d) (hmodel pF hpF).2
  obtain ⟨pF,pQ,pI,hF,hQ,hjoint⟩ := fiberwise_principal_meets_joint_open_with_extra D hD Phi hfiber P hP
  exact ⟨pF,pQ,pI,hjoint,(hmodel pF hF).1,hQ⟩

end Froberg
