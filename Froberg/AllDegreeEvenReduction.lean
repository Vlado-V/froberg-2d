module

public import Froberg.PairedEvenReduction
public import Froberg.PairedLeadingWitnesses
public import Froberg.PreparedSmallLeadingWitnesses
public import Froberg.PreparedAllScalarSmallReduction
public import Froberg.AllScalarEvenReduction
public import Froberg.AllScalarSmallReduction
public import Froberg.AllScalarEvenLeading
public import Froberg.AllScalarSmallLeading

@[expose] public section

/-! The actual scalar/even reduction, uniformly over all degrees at
least three, ordinary output variables, and sufficiently large scalar
dimensions. The output module and its constraints are selected last. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
variable {K : Type} [Field K] [Infinite K]

theorem eventually_actual_all_degree_even_reduction {d : ℕ} (hd : 3≤d) :
    ∀ᶠ h : ℕ in atTop,4∣h → ∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2)) →
      ∀ᶠ n : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → Poly K h →ₗ[K] X,
      finrank K X=deletedTargetCount d h →
      finrank K ↥(Forms K h 2⊓(T 2).ker)=quadraticOutputDimension d h →
      (∀ R,4≤R → T R=0) →
      let A := Space n d (upperCount n d) (allEvenIndices d)
        (allEvenCount d h n (e n+extra)) (fun j => Forms K h j⊓(T j).ker)
      ∃ D : MvPolynomial (Fin (finrank K A)) K,
        (∃ p : A,eval ((Module.finBasis K A).equivFun p) D≠0) ∧
        ∀ p : A,eval ((Module.finBasis K A).equivFun p) D≠0 → EvenPositiveReduction p := by
  by_cases hd9 : 9≤d
  · apply eventually_even_reduction_from_paired hd
    filter_upwards [eventually_actual_even_reduction_open_all_scalars (K := K) hd9] with w hw
    intro _
    exact hw
  by_cases hd5 : 5≤d
  · apply eventually_even_reduction_from_paired hd
    filter_upwards [eventually_actual_middle_all_scalar_reduction_open_late_output (K := K) hd5 (by omega)] with w hw
    intro hdiv extra e he
    filter_upwards [hw hdiv extra e he] with n hn
    intro X _ _ _ T hX hO hT
    exact hn X T hX hO (hT 4 le_rfl)
  have h34 : d=3 ∨ d=4 := by omega
  rcases h34 with rfl | rfl
  · filter_upwards [eventually_actual_cubic_reduction_all_scalars (K := K)] with h hh
    intro _ extra e he
    filter_upwards [hh extra e he] with n hn
    intro X _ _ _ T hX hO _
    exact hn X T hX hO
  · filter_upwards [eventually_actual_quartic_reduction_all_scalars (K := K)] with h hh
    intro _ extra e he
    filter_upwards [hh extra e he] with n hn
    intro X _ _ _ T hX hO _
    exact hn X T hX hO

theorem eventually_actual_all_degree_leading_witnesses {d : ℕ} (hd : 3≤d) :
    ∀ᶠ h : ℕ in atTop,4∣h → ∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2)) →
      ∀ᶠ n : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → Poly K h →ₗ[K] X,
      finrank K X=deletedTargetCount d h →
      finrank K ↥(Forms K h 2⊓(T 2).ker)=quadraticOutputDimension d h →
      (∀ R,4≤R → T R=0) →
      let A := Space n d (upperCount n d) (allEvenIndices d)
        (allEvenCount d h n (e n+extra)) (fun j => Forms K h j⊓(T j).ker)
      ∀ j : allEvenIndices d,∃ p : A,LinearIndependent K (p.2 j) := by
  by_cases hd9 : 9≤d
  · apply eventually_leading_witnesses_from_paired hd
    filter_upwards [eventually_actual_even_leading_witnesses_all_scalars (K := K) hd9] with w hw
    intro _
    exact hw
  by_cases hd5 : 5≤d
  · apply eventually_leading_witnesses_from_paired hd
    filter_upwards [eventually_actual_middle_all_scalar_leading_witnesses_late_output (K := K) hd5 (by omega)] with w hw
    intro hdiv extra e he
    filter_upwards [hw hdiv extra e he] with n hn
    intro X _ _ _ T hX hO hT
    exact hn X T hX hO (hT 4 le_rfl)
  have h34 : d=3 ∨ d=4 := by omega
  rcases h34 with rfl | rfl
  · filter_upwards [eventually_actual_cubic_leading_witnesses_all_scalars (K := K)] with h hh
    intro _ extra e he
    filter_upwards [hh extra e he] with n hn
    intro X _ _ _ T hX hO _
    exact hn X T hX hO
  · filter_upwards [eventually_actual_quartic_leading_witnesses_all_scalars (K := K)] with h hh
    intro _ extra e he
    filter_upwards [hh extra e he] with n hn
    intro X _ _ _ T hX hO _
    exact hn X T hX hO

theorem eventually_actual_all_degree_even_data {d : ℕ} (hd : 3≤d) :
    ∀ᶠ h : ℕ in atTop,4∣h → ∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2)) →
      ∀ᶠ n : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → Poly K h →ₗ[K] X,
      finrank K X=deletedTargetCount d h →
      finrank K ↥(Forms K h 2⊓(T 2).ker)=quadraticOutputDimension d h →
      (∀ R,4≤R → T R=0) →
      let A := Space n d (upperCount n d) (allEvenIndices d)
        (allEvenCount d h n (e n+extra)) (fun j => Forms K h j⊓(T j).ker)
      (∀ j : allEvenIndices d,∃ p : A,LinearIndependent K (p.2 j)) ∧
      ∃ D : MvPolynomial (Fin (finrank K A)) K,
        (∃ p : A,eval ((Module.finBasis K A).equivFun p) D≠0) ∧
        ∀ p : A,eval ((Module.finBasis K A).equivFun p) D≠0 → EvenPositiveReduction p := by
  filter_upwards [eventually_actual_all_degree_even_reduction (K := K) hd,
    eventually_actual_all_degree_leading_witnesses (K := K) hd] with h hr hl
  intro hdiv extra e he
  filter_upwards [hr hdiv extra e he,hl hdiv extra e he] with n hrn hln
  intro X _ _ _ T hX hO hT
  exact ⟨hln X T hX hO hT,hrn X T hX hO hT⟩

end Froberg.PreparedParameters
