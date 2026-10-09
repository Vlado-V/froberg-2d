module

public import Froberg.PreparedCountedRestoredOdd

@[expose] public section

/-! The restored background odd-row open uses a common numerical threshold. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
open scoped Topology

theorem eventually_uniform_restored_odd_injective_open {h d : ℕ} (hd : 2 ≤ d) (he : d%2=0)
    (r : ℕ → ℕ)
    (hr : Tendsto (fun m : ℕ => (r m : ℝ)/(m : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ)))) :
    ∀ᶠ m : ℕ in atTop,∀ (K : Type) [Field K] [Infinite K], ∀ (q : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
      (O : ℕ → Submodule K (Poly K h))
      (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
      (idx : Fin (r m) ≃ Label q J counts)
      (slot : Fin (finrank K (Forms K h d)) → Fin (r m)),
      ∃ D : MvPolynomial (Fin (finrank K (RestoredSpace m d q J counts O))) K,
        (∃ p : RestoredSpace m d q J counts O,eval (restoredCoordinates hO p) D≠0) ∧
        ∀ p : RestoredSpace m d q J counts O,eval (restoredCoordinates hO p) D≠0 →
          Function.Injective (restoredOddRowLinear (restoredFamilyLinear he hO hJ heven idx slot p)) := by
  filter_upwards [eventually_critical_prefix_capacity hd r hr,eventually_gt_atTop (0 : ℕ),
    eventually_ge_atTop ((d-1+d).choose (d-1)*((d-1+d).choose (d-1)*d.choose (d-1)))]
    with m hcap hm hlarge
  intro K _ _ q J counts O hO hJ heven idx slot
  exact restored_odd_injective_principal_open hm (by omega) he hO hJ heven idx slot hlarge hcap


theorem eventually_uniform_counted_restored_odd_open {d : ℕ} (hd : 3 ≤ d) (heven : d%2=0)
    (h extra : ℕ) (e : ℕ → ℕ)
    (he : ∀ᶠ m : ℕ in atTop,(e m : ℝ)<countBeta d*(h : ℝ)^2*(m : ℝ)^(d-2)) :
    ∀ᶠ m : ℕ in atTop,∀ (K : Type) [Field K] [Infinite K],
      ∀ (O : ℕ → Submodule K (Poly K h))
        (hO : ∀ j∈allEvenIndices d,O j≤Forms K h j)
        (idx : Fin (Fintype.card (Label (upperCount m d) (allEvenIndices d)
          (allEvenCount d h m (e m+extra)))) ≃
            Label (upperCount m d) (allEvenIndices d) (allEvenCount d h m (e m+extra)))
        (slot : Fin (finrank K (Forms K h d)) →
          Fin (Fintype.card (Label (upperCount m d) (allEvenIndices d)
            (allEvenCount d h m (e m+extra))))),
      let hJ : ∀ j∈allEvenIndices d,j≤d := fun _ hj => (mem_allEvenIndices.mp hj).2.1
      let hEven : ∀ j∈allEvenIndices d,j%2=0 := fun _ hj => (mem_allEvenIndices.mp hj).2.2
      ∃ D : MvPolynomial (Fin (finrank K (RestoredSpace m d (upperCount m d)
          (allEvenIndices d) (allEvenCount d h m (e m+extra)) O))) K,
        (∃ p : RestoredSpace m d (upperCount m d) (allEvenIndices d)
          (allEvenCount d h m (e m+extra)) O,eval (restoredCoordinates hO p) D≠0) ∧
        ∀ p : RestoredSpace m d (upperCount m d) (allEvenIndices d)
          (allEvenCount d h m (e m+extra)) O,eval (restoredCoordinates hO p) D≠0 →
          Function.Injective (restoredOddRowLinear
            (restoredFamilyLinear heven hO hJ hEven idx slot p)) := by
  let r := fun m => Fintype.card (Label (upperCount m d) (allEvenIndices d)
    (allEvenCount d h m (e m+extra)))
  have hr := allEvenLabel_count_limit hd h extra e he
  filter_upwards [eventually_uniform_restored_odd_injective_open (h := h)
    (by omega) heven r hr] with m hm
  intro K _ _ O hO idx slot
  exact hm K (upperCount m d) (allEvenIndices d) (allEvenCount d h m (e m+extra)) O hO
    (fun _ hj => (mem_allEvenIndices.mp hj).2.1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.2) idx slot


end Froberg.PreparedParameters
