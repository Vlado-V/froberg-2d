module

public import Froberg.ShiftedActualEvenReduction
public import Froberg.NaturalEventualParity

@[expose] public section

/-! The scalar/even background with the actual counts has the literal
positive-row reduction on a nonempty open. This is the U=0 input to even
degree restoration, with any fixed appended quadratic slots included. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
variable {K : Type} [Field K] [Infinite K]
theorem eventually_actual_even_reduction_open_all_scalars {d : ℕ} (hd : 9≤d) :
    ∀ᶠ w : ℕ in atTop,
      ∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ n : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) →
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) →
      (∀ R,4≤R → T R=0) →
        let S := Space n d (upperCount n d) (allEvenIndices d)
          (allEvenCount d (2*w) n (e n+extra)) (constrainedOutputs T)
        ∃ D : MvPolynomial (Fin (finrank K S)) K,
          (∃ p : S,eval ((Module.finBasis K S).equivFun p) D≠0) ∧
          ∀ p : S,eval ((Module.finBasis K S).equivFun p) D≠0 → EvenPositiveReduction p := by
  filter_upwards [eventually_actual_even_reduction_open_shift_uniform (K := K) hd] with w hw
  intro extra e he
  exact eventually_of_twice_add_shifts 0 _
    (hw 0 extra e he) (hw 1 extra e he)

end Froberg.PreparedParameters
