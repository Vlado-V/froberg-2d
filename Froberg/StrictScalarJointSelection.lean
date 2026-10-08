import Froberg.StrictScalarInjection
import Froberg.LinearFiberwisePrincipal

/-! A strict vector-model open and the scalar quotient injection can be
chosen on any prescribed nonempty joint coefficient open. -/
noncomputable section
namespace Froberg.VectorExpansionOpen
open Module MvPolynomial Quartic VectorMultiplicationCoordinates
variable {K : Type} [Field K] [Infinite K] {h n s d c q : ℕ} {G : ℝ}

theorem strict_scalar_joint_selection
    (D : MvPolynomial (Fin (finrank K (Fin c → Rows K h n s))) K)
    (hD : ∃ g : Fin c → Rows K h n s,eval ((Module.finBasis K _).equivFun g) D≠0)
    (hmodel : ∀ g : Fin c → Rows K h n s,eval ((Module.finBasis K _).equivFun g) D≠0 →
      StrictModel g d G ∧ q*finrank K (Source g)≤finrank K (Target g d))
    (P : MvPolynomial (Fin (finrank K ((Fin c → Rows K h n s) × (Fin q → Forms K n d)))) K)
    (hP : ∃ p : (Fin c → Rows K h n s) × (Fin q → Forms K n d),
      eval ((Module.finBasis K _).equivFun p) P≠0) :
    ∃ (g : Fin c → Rows K h n s) (Q : Fin q → Forms K n d),
      StrictModel g d G ∧
      Function.Injective (BilinearScalarFamily.multiplication (quotientMultiplication g d) Q) ∧
      eval ((Module.finBasis K _).equivFun (g,Q)) P≠0 := by
  have hfiber : ∀ g : Fin c → Rows K h n s,eval ((Module.finBasis K _).equivFun g) D≠0 →
      ∃ E : MvPolynomial (Fin (finrank K (Fin q → Forms K n d))) K,
        (∃ Q : Fin q → Forms K n d,eval ((Module.finBasis K _).equivFun Q) E≠0) ∧
        ∀ Q,eval ((Module.finBasis K _).equivFun Q) E≠0 →
          Function.Injective (BilinearScalarFamily.multiplication (quotientMultiplication g d) Q) := by
    intro g hg
    exact (hmodel g hg).1.generic_scalar_injective (hmodel g hg).2
  obtain ⟨g,Q,hg,hQ,hjoint⟩ := fiberwise_principal_meets_linear_joint_open D hD _ hfiber P hP
  exact ⟨g,Q,(hmodel g hg).1,hQ,hjoint⟩

end Froberg.VectorExpansionOpen
