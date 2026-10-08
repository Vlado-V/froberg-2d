import Froberg.PreparedQuadraticRow
import Froberg.QuadraticSparseBudget
import Froberg.ShiftedCountLimits
import Froberg.PrefixInjectionOpen
import Froberg.ScalarSeparationAsymptotic

/-! Actual quadratic finite-capacity records, including any fixed appended
private slots, follow from the established asymptotic count estimates. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
open Quartic.PolynomialBilinearCoordinates
open scoped Topology
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ]

theorem eventually_quadratic_capacity_shift {d : ℕ} (hd : 3≤d) :
    ∀ᶠ h : ℕ in atTop,∀ (σ : Type*) [Fintype σ],∀ (O : ℕ → Submodule K (MvPolynomial σ K)),
      finrank K (O 2)=quadraticOutputDimension d h →
      ∀ (J : Finset ℕ) (q : ℕ → ℕ) (counts : ℕ → ℕ → ℕ),
      Tendsto (fun n : ℕ => (Fintype.card (Label (q n) J (counts n)) : ℝ)/(n : ℝ)^d)
        atTop (𝓝 (criticalRatio d/(d.factorial : ℝ))) →
      ∀ z extra : ℕ,∀ᶠ n : ℕ in atTop,
        counts n 2≤⌈countBeta d*(h : ℝ)^2*((n+z : ℕ) : ℝ)^(d-2)⌉₊+extra →
        QuadraticRowCapacity n d (q n) (fullSparseBlockCount (countBeta d) 2 (d-2) h)
          J (counts n) O := by
  have hβ : 0≤countBeta d := by
    have hG := (countTauFour_pos hd).trans_le (countTauFour_le_gamma d)
    unfold countBeta
    positivity
  filter_upwards [eventually_quadratic_sparse_layer_budget hd,
    eventually_gt_atTop (0 : ℕ)] with h hh hhpos
  intro σ inst O hO J q counts hcount z extra
  let r := fun n => Fintype.card (Label (q n) J (counts n))
  have hbudget := hh.2.2 r hcount
  have hscalar := eventually_critical_scalar_incidence_budget (by omega : 2≤d) r hcount
  have hcover := fullSparseBlockCount_eventually_covers_shift_add (countBeta d) hβ 2 h z extra
    (by omega : 0<d-2)
  filter_upwards [hbudget,hscalar,hcover,eventually_gt_atTop (0 : ℕ),
    eventually_ge_atTop ((d-2+d).choose (d-2)*((d-2+d).choose (d-2)*d.choose (d-2)))]
    with n hbudget hscalar hcover hn hlarge
  intro hc
  have hinc := (hbudget 0 (by
    have hp : 0<countBeta d := by
      have hG := (countTauFour_pos hd).trans_le (countTauFour_le_gamma d)
      unfold countBeta
      positivity
    simpa only [Nat.cast_zero] using mul_pos (mul_pos hp (pow_pos (show (0:ℝ)<(h:ℝ) from by exact_mod_cast hhpos) 2))
      (pow_pos (show (0:ℝ)<(n:ℝ) from by exact_mod_cast hn) (d-2)))).2
  have hr : r n*(n+(d-2)-1).choose (d-2)≤(n+(d+(d-2))-1).choose (d+(d-2)) := by
    have he : 2*d-2=d+(d-2) := by omega
    rw [he] at hscalar
    nlinarith
  obtain ⟨D,hD,hgood⟩ := prefix_injective_principal_open (K := K) hn
    (by omega : d-2<d) hlarge hr
  exact { variables_positive := hn
          output_positive := by simpa only [hO] using hh.1
          enough_generators := hc.trans hcover
          divisor_capacity := by simpa only [hO] using hh.2.1
          incidence := by simpa only [hO,r] using hinc
          scalar_open := ⟨D,hD,hgood⟩ }

end Froberg.PreparedParameters
