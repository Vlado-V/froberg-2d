module

public import Froberg.ActualSmallExtendedReduction
public import Froberg.NaturalEventualParity

@[expose] public section

/-! Both scalar-dimension parity classes are covered by the actual cubic
and quartic prepared-family opens. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
open scoped Topology
variable {K : Type} [Field K] [Infinite K]
theorem eventually_actual_cubic_reduction_all_scalars :
    ∀ᶠ h : ℕ in atTop,
      ∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta 3*(h : ℝ)^2*(n : ℝ)^(3-2)) →
      ∀ᶠ n : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → Poly K h →ₗ[K] X,
      finrank K X=deletedTargetCount 3 h →
      finrank K ↥(Forms K h 2⊓(T 2).ker)=quadraticOutputDimension 3 h →
        let A := Space n 3 (upperCount n 3) (allEvenIndices 3)
          (allEvenCount 3 h n (e n+extra))
          (fun j => Forms K h j⊓(T j).ker)
        ∃ D : MvPolynomial (Fin (finrank K A)) K,
          (∃ p : A,eval ((Module.finBasis K A).equivFun p) D≠0) ∧
          ∀ p : A,eval ((Module.finBasis K A).equivFun p) D≠0 → EvenPositiveReduction p := by
  filter_upwards [eventually_actual_cubic_extended_reduction_open (K := K)] with h hh
  intro extra e he
  exact eventually_of_twice_add_shifts 0 _
    (hh 0 extra e he) (hh 1 extra e he)

theorem eventually_actual_quartic_reduction_all_scalars :
    ∀ᶠ h : ℕ in atTop,
      ∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta 4*(h : ℝ)^2*(n : ℝ)^(4-2)) →
      ∀ᶠ n : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → Poly K h →ₗ[K] X,
      finrank K X=deletedTargetCount 4 h →
      finrank K ↥(Forms K h 2⊓(T 2).ker)=quadraticOutputDimension 4 h →
        let A := Space n 4 (upperCount n 4) (allEvenIndices 4)
          (allEvenCount 4 h n (e n+extra))
          (fun j => Forms K h j⊓(T j).ker)
        ∃ D : MvPolynomial (Fin (finrank K A)) K,
          (∃ p : A,eval ((Module.finBasis K A).equivFun p) D≠0) ∧
          ∀ p : A,eval ((Module.finBasis K A).equivFun p) D≠0 → EvenPositiveReduction p := by
  filter_upwards [eventually_actual_quartic_extended_reduction_open (K := K)] with h hh
  intro extra e he
  exact eventually_of_twice_add_shifts 0 _
    (hh 0 extra e he) (hh 1 extra e he)

end Froberg.PreparedParameters
