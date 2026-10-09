module

public import Froberg.PreparedFiniteRows
public import Froberg.PreparedFiniteProducts
public import Froberg.IntermediateScalarBudget
public import Froberg.ParityProfileScalar

@[expose] public section

/-! Rows with no new generators still have their scalar/product equation.
The zero sparse-block count handles them, including the row of degree d. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
open Quartic.PolynomialBilinearCoordinates
open scoped Topology
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem eventually_empty_higher_capacity {w d : ℕ} (hd : 9≤d)
    (J : Finset ℕ) (R : J) (hR : 4≤R.val) (hRd : R.val≤d)
    (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X) (hTR : T R.val=0)
    (hH : 0<oddOutputDimension w R.val)
    (q : ℕ → ℕ) (counts : ℕ → ℕ → ℕ)
    (hzero : ∀ n,counts n R.val=0)
    (hr : Tendsto (fun n : ℕ => (Fintype.card (Label (q n) J (counts n)) : ℝ)/(n : ℝ)^d)
      atTop (𝓝 (criticalRatio d/(d.factorial : ℝ)))) :
    ∀ᶠ v : ℕ in atTop,
      ProductRowCapacity (K := K) (X := X) w v d R.val J (counts (v+v)) →
      (∀ j∈J,0<j) →
      HigherRowCapacity w v d (q (v+v)) 0 J (counts (v+v)) T R := by
  let r := fun n => Fintype.card (Label (q n) J (counts n))
  have hratio : (((d-R.val)+d).choose (d-R.val) : ℝ)*criticalRatio d<1 := by
    have hb := higher_scalar_source_bound hR hRd
    have he : 2*d-R.val=(d-R.val)+d := by omega
    simpa only [scalarCapacityBinomial,he] using hb.trans (by norm_num : (1/8 : ℝ)<1)
  have hgap : (0 : ℝ)+(oddOutputDimension w R.val : ℝ)*
      (((d-R.val)+d).choose (d-R.val) : ℝ)*criticalRatio d<oddOutputDimension w R.val := by
    have hp : (0 : ℝ)<oddOutputDimension w R.val := by exact_mod_cast hH
    nlinarith
  have hbudget := eventually_intermediate_scalar_budget (by omega : d-R.val<d)
    (Nat.zero_le (oddOutputDimension w R.val)) r hr (by simpa only [Nat.cast_zero] using hgap)
  obtain ⟨n₀,hn₀⟩ := eventually_generic_profile_scalar_separation (K := K) hd
    (show d-R.val+4≤d by omega) r hr
  obtain ⟨n₁,hn₁⟩ := eventually_atTop.mp hbudget
  filter_upwards [eventually_ge_atTop (max n₀ n₁)] with v hv
  intro hp hpositive
  obtain ⟨D,hD,hgood⟩ := hn₀ (v+v) (by omega) (balancedScalarHalf v)
    (by simp only [balancedScalarHalf_card,balancedScalarHalf_compl_card]; omega)
    (by simp only [balancedScalarHalf_card,balancedScalarHalf_compl_card];omega)
    (d%2) (Nat.mod_lt d (by decide)) (2*((d-R.val/2)/2))
  exact { hw := hp.positive_output
          hv := hp.positive_scalar
          positive := hpositive
          even := hp.even_degrees
          degree := hp.bounded_degrees
          new_unconstrained := hTR
          diagonal := hp.diagonal
          cross := hp.cross
          output_positive := hH
          enough_generators := by rw [hzero];simp
          divisor_capacity := by simp
          incidence := by simpa only [zero_mul,Nat.sub_zero,r] using hn₁ (v+v) (by omega)
          scalar_open := ⟨D,hD,fun Q hQ => (hgood Q hQ).1⟩ }

end Froberg.PreparedParameters
