module

public import Froberg.RestoredOddOpen
public import Froberg.CriticalPrefixCapacity

@[expose] public section

/-! The actual restored all-even parameter family has an odd-cycle injection
open for every sufficiently large scalar variable count at critical density. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
open scoped Topology
variable {K : Type} [Field K] [Infinite K] {h d : ℕ}

theorem eventually_restored_odd_injective_open (hd : 2 ≤ d) (he : d%2=0)
    (r : ℕ → ℕ)
    (hr : Tendsto (fun m : ℕ => (r m : ℝ)/(m : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ)))) :
    ∀ᶠ m : ℕ in atTop,∀ (q : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
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
  intro q J counts O hO hJ heven idx slot
  exact restored_odd_injective_principal_open hm (by omega) he hO hJ heven idx slot hlarge hcap

end Froberg.PreparedParameters
