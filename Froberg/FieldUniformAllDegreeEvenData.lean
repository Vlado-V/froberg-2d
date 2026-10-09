module

public import Froberg.FieldUniformPairedData
public import Froberg.FieldUniformMiddleData
public import Froberg.FieldUniformEvenData
public import Froberg.FieldUniformSmallData

@[expose] public section

noncomputable section
set_option maxHeartbeats 1800000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter

theorem eventually_field_uniform_all_degree_even_data {d : ℕ} (hd : 3≤d) :
    ∀ᶠ h : ℕ in atTop,4∣h → ∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2)) →
      ∀ᶠ n : ℕ in atTop,
      ∀ (K : Type) [Field K] [Infinite K],
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
  by_cases hd9 : 9≤d
  · apply eventually_field_uniform_even_data_from_paired hd
    filter_upwards [eventually_field_uniform_even_all_scalar_data hd9] with w hw
    intro _
    exact hw
  by_cases hd5 : 5≤d
  · apply eventually_field_uniform_even_data_from_paired hd
    filter_upwards [eventually_field_uniform_middle_all_scalar_data hd5 (by omega)] with w hw
    intro hdiv extra e he
    filter_upwards [hw hdiv extra e he] with n hn
    intro K _ _ X _ _ _ T hX hO hT
    exact hn K X T hX hO (hT 4 le_rfl)
  have h34 : d=3 ∨ d=4 := by omega
  rcases h34 with rfl | rfl
  · filter_upwards [eventually_field_uniform_cubic_all_scalar_data] with h hh
    intro _ extra e he
    filter_upwards [hh extra e he] with n hn
    intro K _ _ X _ _ _ T hX hO _
    exact hn K X T hX hO
  · filter_upwards [eventually_field_uniform_quartic_all_scalar_data] with h hh
    intro _ extra e he
    filter_upwards [hh extra e he] with n hn
    intro K _ _ X _ _ _ T hX hO _
    exact hn K X T hX hO

end Froberg.PreparedParameters
