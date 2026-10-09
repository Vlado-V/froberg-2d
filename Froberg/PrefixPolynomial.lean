module

public import Froberg.BinomialPolynomial
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# The numerical condition in the asymptotic prefix theorem

For fixed degrees, the sufficient polynomial inequality in Theorem 4 of
Boij–Dannetun–Lundqvist eventually holds by elementary real analysis. This
avoids the coefficient sign analysis, which is needed for their stronger
uniform and explicit numerical bounds but not for a fixed generating degree.
-/

noncomputable section
namespace Froberg
open Polynomial Filter Set
open scoped Topology

/-- A real polynomial with positive leading coefficient is eventually positive,
including the constant case. -/
theorem polynomial_eventually_positive (P : ℝ[X]) (hP : 0 < P.leadingCoeff) :
    ∀ᶠ x : ℝ in atTop, 0 < P.eval x := by
  by_cases hd : P.natDegree = 0
  · have he : P = C P.leadingCoeff := by
      simpa only [Polynomial.leadingCoeff, hd] using eq_C_of_natDegree_eq_zero hd
    apply Eventually.of_forall
    intro x
    conv_rhs => rw [he, eval_C]
    exact hP
  · have hp : 0 < P.degree := natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)
    exact (P.tendsto_atTop_of_leadingCoeff_nonneg hp hP.le).eventually_gt_atTop 0

/-- Every nonconstant positive-leading polynomial eventually reaches its
maximum on `[0,y]` at the right endpoint `y`. -/
theorem polynomial_eventually_maximum_on_prefix (P : ℝ[X])
    (hdeg : 0 < P.natDegree) (hlead : 0 < P.leadingCoeff) :
    ∀ᶠ y : ℝ in atTop, ∀ x : ℝ, 0 ≤ x → x ≤ y → P.eval x ≤ P.eval y := by
  have hderiv : 0 < P.derivative.leadingCoeff := by
    rw [leadingCoeff_derivative]
    exact mul_pos hlead (by exact_mod_cast hdeg)
  obtain ⟨a, ha⟩ := (eventually_atTop.mp (polynomial_eventually_positive P.derivative hderiv))
  let b : ℝ := max 0 a
  have hb0 : 0 ≤ b := le_max_left _ _
  have hba : a ≤ b := le_max_right _ _
  have hmono : MonotoneOn P.eval (Ici b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici b) P.continuous.continuousOn
    · intro x _
      exact (P.hasDerivAt x).hasDerivWithinAt
    · intro x hx
      exact (ha x (hba.trans (interior_subset hx))).le
  obtain ⟨c, hc⟩ := isCompact_Icc.bddAbove_image (P.continuous.continuousOn :
    ContinuousOn P.eval (Icc 0 b))
  have hlim := P.tendsto_atTop_of_leadingCoeff_nonneg
    (natDegree_pos_iff_degree_pos.mp hdeg) hlead.le
  filter_upwards [hlim.eventually_ge_atTop c, eventually_ge_atTop b] with y hyc hyb
  intro x hx0 hxy
  by_cases hbx : b ≤ x
  · exact hmono hbx hyb hxy
  · exact (hc ⟨x, ⟨hx0, le_of_not_ge hbx⟩, rfl⟩).trans hyc

/-- The polynomial `g_{d,e}` of Boij–Dannetun–Lundqvist, in their coordinate
`x=n-1`. Here `e` is their `d′`. -/
def prefixComparisonPolynomial (d e : ℕ) : ℝ[X] :=
  C (((d + e).choose d : ℝ)⁻¹) *
      (monomialCountPolynomial d).comp (X + C ((e : ℝ) + 1)) -
    (monomialCountPolynomial e).comp (X + C 1)

theorem prefixComparisonPolynomial_natDegree {d e : ℕ} (hed : e < d) :
    (prefixComparisonPolynomial d e).natDegree = d := by
  have hc : ((d + e).choose d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : d ≤ d + e)).ne'
  have hA : (C (((d + e).choose d : ℝ)⁻¹) *
      (monomialCountPolynomial d).comp (X + C ((e : ℝ) + 1))).natDegree = d := by
    rw [natDegree_C_mul (inv_ne_zero hc), natDegree_comp, natDegree_X_add_C]
    simp [monomialCountPolynomial_natDegree]
  have hB : ((monomialCountPolynomial e).comp (X + C 1)).natDegree = e := by
    rw [natDegree_comp]
    simp [monomialCountPolynomial_natDegree]
  unfold prefixComparisonPolynomial
  exact (natDegree_sub_eq_left_of_natDegree_lt (by rw [hA, hB]; exact hed)).trans hA

theorem prefixComparisonPolynomial_leadingCoeff {d e : ℕ} (hed : e < d) :
    (prefixComparisonPolynomial d e).leadingCoeff =
      ((d + e).choose d : ℝ)⁻¹ * (d.factorial : ℝ)⁻¹ := by
  have hc : ((d + e).choose d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : d ≤ d + e)).ne'
  have hA : (C (((d + e).choose d : ℝ)⁻¹) *
      (monomialCountPolynomial d).comp (X + C ((e : ℝ) + 1))).natDegree = d := by
    rw [natDegree_C_mul (inv_ne_zero hc), natDegree_comp, natDegree_X_add_C]
    simp [monomialCountPolynomial_natDegree]
  have hB : ((monomialCountPolynomial e).comp (X + C 1)).natDegree = e := by
    rw [natDegree_comp]
    simp [monomialCountPolynomial_natDegree]
  have hlt : ((monomialCountPolynomial e).comp (X + C 1)).degree <
      (C (((d + e).choose d : ℝ)⁻¹) *
        (monomialCountPolynomial d).comp (X + C ((e : ℝ) + 1))).degree :=
    degree_lt_degree (by rw [hA, hB]; exact hed)
  unfold prefixComparisonPolynomial
  rw [leadingCoeff_sub_of_degree_lt hlt, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_comp (by rw [natDegree_X_add_C]; omega), leadingCoeff_X_add_C]
  simp [monomialCountPolynomial_leadingCoeff]

/-- The real-variable sufficient inequality in BDL Theorem 4 holds eventually
for every pair of degrees `e<d`; no sign-pattern hypothesis is needed. -/
theorem prefixComparisonPolynomial_eventually_maximum {d e : ℕ} (hed : e < d) :
    ∀ᶠ y : ℝ in atTop, ∀ x : ℝ, 0 ≤ x → x ≤ y →
      (prefixComparisonPolynomial d e).eval x ≤ (prefixComparisonPolynomial d e).eval y := by
  apply polynomial_eventually_maximum_on_prefix
  · rw [prefixComparisonPolynomial_natDegree hed]
    omega
  · rw [prefixComparisonPolynomial_leadingCoeff hed]
    have hc : 0 < ((d + e).choose d : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : d ≤ d + e)
    have hf : 0 < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
    positivity

/-- The comparison polynomial measures the surplus of the target-to-multiplier
ratio over the dimension of the multiplier space. -/
theorem prefixComparisonPolynomial_eval {n : ℕ} (hn : 0 < n) (d e : ℕ) :
    (prefixComparisonPolynomial d e).eval ((n : ℝ) - 1) =
      ((n + (d + e) - 1).choose (d + e) : ℝ) / ((n + e - 1).choose e : ℝ) -
        ((n + e - 1).choose e : ℝ) := by
  have hC : ((d + e).choose d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : d ≤ d + e)).ne'
  have hE : ((n + e - 1).choose e : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : e ≤ n + e - 1)).ne'
  have hprod := Nat.choose_mul (n := n + (d + e) - 1) (k := d + e) (s := d)
    (by omega)
  rw [show n + (d + e) - 1 - d = n + e - 1 by omega,
    show d + e - d = e by omega] at hprod
  have hprodR : ((n + (d + e) - 1).choose (d + e) : ℝ) * ((d + e).choose d : ℝ) =
      ((n + (d + e) - 1).choose d : ℝ) * ((n + e - 1).choose e : ℝ) := by
    exact_mod_cast hprod
  unfold prefixComparisonPolynomial
  simp only [eval_sub, eval_mul, eval_C, eval_comp, eval_add, eval_X]
  rw [show (n : ℝ) - 1 + ((e : ℝ) + 1) = ((n + e : ℕ) : ℝ) by push_cast; ring,
    show (n : ℝ) - 1 + 1 = (n : ℝ) by ring,
    monomialCountPolynomial_eval, monomialCountPolynomial_eval,
    show n + e + d - 1 = n + (d + e) - 1 by omega]
  congr 1
  field_simp
  nlinarith

/-- Numerical surplus and the square-dimension condition are equivalent. -/
theorem prefixComparisonPolynomial_nonneg_iff {n : ℕ} (hn : 0 < n) (d e : ℕ) :
    0 ≤ (prefixComparisonPolynomial d e).eval ((n : ℝ) - 1) ↔
      ((n + e - 1).choose e)^2 ≤ (n + (d + e) - 1).choose (d + e) := by
  rw [prefixComparisonPolynomial_eval hn]
  have hE : 0 < ((n + e - 1).choose e : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : e ≤ n + e - 1)
  rw [sub_nonneg, le_div_iff₀ hE]
  norm_cast
  rw [pow_two]

/-- A concrete existential threshold for the complete numerical hypothesis
in BDL Theorem 4, expressed at integral variable counts. -/
theorem exists_prefixComparison_threshold {d e : ℕ} (hed : e < d) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      0 ≤ (prefixComparisonPolynomial d e).eval ((n : ℝ) - 1) ∧
      ∀ x : ℝ, 0 ≤ x → x ≤ (n : ℝ) - 1 →
        (prefixComparisonPolynomial d e).eval x ≤
          (prefixComparisonPolynomial d e).eval ((n : ℝ) - 1) := by
  have hlead : 0 < (prefixComparisonPolynomial d e).leadingCoeff := by
    rw [prefixComparisonPolynomial_leadingCoeff hed]
    have hc : 0 < ((d + e).choose d : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : d ≤ d + e)
    have hf : 0 < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
    positivity
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop)
  apply eventually_atTop.mp
  filter_upwards [hlim.eventually (polynomial_eventually_positive _ hlead),
    hlim.eventually (prefixComparisonPolynomial_eventually_maximum hed)] with n hn hmax
  exact ⟨hn.le, hmax⟩

end Froberg
