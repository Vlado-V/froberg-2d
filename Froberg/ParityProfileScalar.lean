module

public import Froberg.ParityProfileGrowth
public import Froberg.ProjectedPrefix
public import Froberg.ScalarSeparationAsymptotic
public import Froberg.CapacityBinomial

@[expose] public section

/-! The common scalar list is generically injective after removing all
product profiles in a row of B.4. -/
noncomputable section
namespace Froberg
open Polynomial Filter Module MvPolynomial
open Quartic.PolynomialBilinearCoordinates
open scoped Topology

theorem profile_scalar_leading_gap {d e : ℕ} (he : e+4≤d) :
    4 * (e.factorial : ℝ)⁻¹ * (criticalRatio d / (d.factorial : ℝ)) <
      ((e+d).factorial : ℝ)⁻¹ := by
  have hr := higher_scalar_source_bound (d := d) (j := d-e) (by omega) (by omega)
  have hc : ((e+d).choose d : ℝ) * criticalRatio d < 1/8 := by
    have hs : (e+d).choose e = (e+d).choose d := Nat.choose_symm_of_eq_add rfl
    simpa only [scalarCapacityBinomial, show 2*d-(d-e)=e+d by omega,
      show d-(d-e)=e by omega, hs] using hr
  have hcr : 4 * criticalRatio d * ((e+d).choose d : ℝ) < 1 := by nlinarith
  have hf : ((e+d).choose d : ℝ) * (d.factorial : ℝ) * (e.factorial : ℝ) =
      (e+d).factorial := by
    exact_mod_cast (show (e+d).choose d * d.factorial * e.factorial = (e+d).factorial by
      simpa only [show e+d-d=e by omega] using
        Nat.choose_mul_factorial_mul_factorial (show d≤e+d by omega))
  have hD : (0 : ℝ)<(e+d).factorial := by exact_mod_cast Nat.factorial_pos _
  have hE : (0 : ℝ)<e.factorial := by exact_mod_cast Nat.factorial_pos _
  have hd' : (0 : ℝ)<d.factorial := by exact_mod_cast Nat.factorial_pos _
  apply (mul_lt_mul_iff_left₀ hD).mp
  have heq : (4 * (e.factorial : ℝ)⁻¹ * (criticalRatio d / (d.factorial : ℝ))) *
      (e+d).factorial = 4 * criticalRatio d * ((e+d).choose d : ℝ) := by
    rw [← hf]
    field_simp
  rw [heq]
  simpa only [inv_mul_cancel₀ hD.ne'] using hcr

theorem eventually_profile_scalar_incidence_budget {d e : ℕ} (he : e+4≤d)
    (r : ℕ → ℕ)
    (hr : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d / (d.factorial : ℝ)))) :
    ∀ᶠ n : ℕ in atTop,
      4 * (n+e-1).choose e * ((n+e-1).choose e+r n) ≤
        (n+(e+d)-1).choose (e+d) := by
  have hleft := ((monomial_count_normalized_tendsto e).const_mul 4).mul
    ((monomial_count_normalized_small_tendsto (show e<d by omega)).add hr)
  simp only [zero_add] at hleft
  have hright := monomial_count_normalized_tendsto (e+d)
  filter_upwards [hleft.eventually_lt hright (profile_scalar_leading_gap he),
    eventually_gt_atTop 0] with n hn hnpos
  have hnp : (0 : ℝ)<n := by exact_mod_cast hnpos
  have hpow : (0 : ℝ)<(n : ℝ)^(e+d) := pow_pos hnp _
  have heq :
      4 * (((n+e-1).choose e : ℝ)/(n : ℝ)^e) *
        (((n+e-1).choose e : ℝ)/(n : ℝ)^d + (r n : ℝ)/(n : ℝ)^d) =
      (4 * ((n+e-1).choose e : ℝ) * ((n+e-1).choose e+r n))/(n : ℝ)^(e+d) := by
    rw [pow_add]
    field_simp
  rw [heq] at hn
  have h := (div_lt_div_iff_of_pos_right hpow).mp hn
  exact_mod_cast h.le

/-- A nonempty principal open of the common scalar parameter space works
in the quotient by one parity and one additional profile. -/
theorem eventually_generic_profile_scalar_separation
    {K : Type*} [Field K] [Infinite K] {d e : ℕ} (hd : 9≤d) (he : e+4≤d)
    (r : ℕ → ℕ)
    (hr : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d / (d.factorial : ℝ)))) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ S : Finset (Fin n),
      S.card≤Sᶜ.card → Sᶜ.card≤S.card+1 → ∀ p<2, ∀ j : ℕ,
      ∃ Q : MvPolynomial (Fin (finrank K (Fin (r n) → Forms K n d))) K,
        (∃ f : Fin (r n) → Forms K n d, eval (coordinates K _ f) Q ≠ 0) ∧
        ∀ f : Fin (r n) → Forms K n d, eval (coordinates K _ f) Q ≠ 0 →
          Function.Injective (ProjectedPrefix.multiplication (parityProfileRetained S p j) f e) ∧
          Disjoint (familySpace f * Forms K n e)
            (retainMonomials (K := K) (parityProfileRetained S p j)).ker := by
  obtain ⟨m₀,hm₀⟩ := exists_parity_profile_growth_threshold hd e
  obtain ⟨n₁,hn₁⟩ := eventually_atTop.mp (eventually_profile_scalar_incidence_budget he r hr)
  refine ⟨max (2*m₀+1) n₁,?_⟩
  intro n hn S hle hupper p hp j
  have hcard : S.card+Sᶜ.card=n := by simpa using Finset.card_add_card_compl S
  have hm : m₀≤S.card := by omega
  have hnpos : 0<n := by omega
  obtain ⟨Q,hQ,hgood⟩ := ProjectedPrefix.generic_injective_of_growth
    (K := K) (d := d) (e := e) (r := r n) (parityProfileRetained S p j) hnpos 1 4
    (by norm_num) (by
      intro U hU
      simpa only [one_mul] using hm₀ K n S hm hle hupper U hU p hp j)
    (by simpa only [one_mul] using hn₁ n (by omega))
  refine ⟨Q,hQ,?_⟩
  intro f hf
  have h := hgood f hf
  exact ⟨h,ProjectedPrefix.scalar_product_disjoint_kernel _ f h⟩

end Froberg
