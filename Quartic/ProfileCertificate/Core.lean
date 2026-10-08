import Quartic.FiniteCounts

/-!
# Integral profile inequalities in dimensions 28 through 40

The formulas in this module are the numerical quantities `Phi` and `C` in the
manuscript's profile-incidence argument. The finite claims are checked by the
Lean kernel. This module makes no assertion that the numerical formulas bound
ranks or dimensions of geometric loci; that interpretation is a separate proof.
-/

namespace Quartic.ProfileCertificate

open Quartic.Counts Quartic.FiniteCounts

/-- Core parameter `p = c - 3`. -/
def coreP (c : ℕ) : ℕ := c - 3
/-- Core degree-one dimension `A = 2p`. -/
def coreA (c : ℕ) : ℕ := 2 * coreP c
/-- Free-variable dimension `w = m - c + 2`. -/
def freeW (m c : ℕ) : ℕ := m - c + 2
/-- Core degree-two dimension `B = choose (p+1) 2`. -/
def coreB (c : ℕ) : ℤ := quadratics (coreP c)
/-- Total degree-one source dimension. -/
def totalA (m c : ℕ) : ℕ := coreA c + 3 * freeW m c
/-- Profile dimension `d = i + n₁ + n₂ + n₃`. -/
def profileDim (i n₁ n₂ n₃ : ℕ) : ℕ := i + n₁ + n₂ + n₃
/-- The integral ceiling formula for `Gamma(i)`. -/
def gamma (c i : ℕ) : ℤ :=
  (coreB c * (i : ℤ) + (coreA c : ℤ) - 1) / (coreA c : ℤ)
/-- Number of quadratic free monomials meeting a set of `n` variables. -/
def h2 (w n : ℕ) : ℤ := quadratics w - quadratics (w - n)
/-- Number of cubic free monomials meeting a set of `n` variables. -/
def h3 (w n : ℕ) : ℤ := cubics w - cubics (w - n)

/-- The profile image lower-bound expression, exactly as in `pc:profile`. -/
def Phi (m c i n₁ n₂ n₃ : ℕ) : ℤ :=
  let w := freeW m c
  let p := coreP c
  let A := coreA c
  let e₁ := (max i p : ℤ) - (i : ℤ)
  let e₂ := (A : ℤ) - (max i p : ℤ)
  ((w : ℤ) - (n₁ : ℤ)) * gamma c i + coreB c * (n₁ : ℤ) +
    (i : ℤ) * quadratics w + e₁ * h2 w n₁ + e₂ * h2 w n₂ +
    h3 w n₁ + h3 w n₂ + h3 w n₃

/-- The compressed stratum-dimension expression in `pc:cell`. -/
def Cell (m c i n₁ n₂ n₃ : ℕ) : ℤ :=
  let w := freeW m c
  let A := coreA c
  let s := (n₁ : ℤ) + (n₂ : ℤ) + (n₃ : ℤ)
  let z := (n₁ : ℤ) + 3 * (n₂ : ℤ) + 5 * (n₃ : ℤ)
  let V := (n₁ : ℤ) * (w : ℤ) - quadratics n₁ +
    ((n₂ : ℤ) * (w : ℤ) - quadratics n₂) +
    ((n₃ : ℤ) * (w : ℤ) - quadratics n₃)
  (i : ℤ) * ((A : ℤ) - (i : ℤ)) + s * ((A : ℤ) - (i : ℤ)) +
    3 * s - z + 3 * V - (s * s - z) / 2

/-- Efficient computational expression for the original outer Euler dimension. -/
def outerJ (m q c : ℕ) : ℤ :=
  3 * (cubics m - (m : ℤ) * (q : ℤ)) -
    (c : ℤ) * (quadratics m - (q : ℤ))

theorem coreB_eq_binomial (c : ℕ) :
    coreB c = (Nat.choose (coreP c + 1) 2 : ℤ) := by
  exact quadratics_eq_b2 (coreP c)

theorem h2_eq_binomial (w n : ℕ) :
    h2 w n = (Nat.choose (w + 1) 2 : ℤ) - Nat.choose (w - n + 1) 2 := by
  simp only [h2, quadratics_eq_b2, b2]

theorem h3_eq_binomial (w n : ℕ) :
    h3 w n = (Nat.choose (w + 2) 3 : ℤ) - Nat.choose (w - n + 2) 3 := by
  simp only [h3, cubics_eq_b3, b3]

theorem outerJ_eq_j (m q c : ℕ) : outerJ m q c = j m q c := by
  simp only [outerJ, cubics_eq_b3, quadratics_eq_b2, j, beta, alpha]

/-- For positive denominators, the integer division formula is precisely the
ceiling of the rational quotient. -/
theorem ceiling_division_formula (x : ℤ) (a : ℕ) (ha : 0 < a) :
    (x + (a : ℤ) - 1) / (a : ℤ) = ⌈(x : ℚ) / (a : ℚ)⌉ := by
  rw [Rat.ceil_intCast_div_natCast]
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  rw [Int.ediv_eq_iff_of_pos ha']
  have h := Int.emod_add_mul_ediv (-x) (a : ℤ)
  have hlo := Int.emod_nonneg (-x) (ne_of_gt ha')
  have hhi := Int.emod_lt_of_pos (-x) ha'
  constructor <;> nlinarith

/-- `gamma` agrees with the manuscript's ceiling, with no rounding convention
left implicit. -/
theorem gamma_eq_ceiling (c i : ℕ) (hc : 4 ≤ c) :
    gamma c i = ⌈((coreB c : ℚ) * (i : ℚ)) / (coreA c : ℚ)⌉ := by
  have hA : 0 < coreA c := by unfold coreA coreP; omega
  simpa only [gamma, Int.cast_mul, Int.cast_natCast] using
    ceiling_division_formula (coreB c * (i : ℤ)) (coreA c) hA

/-- Agreement of the free-variable dimension with `w = m - t`, `t = c - 2`. -/
theorem freeW_eq_sub_core (m c : ℕ) (hc : 4 ≤ c) (hcm : c ≤ m) :
    freeW m c = m - (c - 2) := by
  unfold freeW
  omega

/-- Agreement of the total degree-one dimension with `a = 3m - c`. -/
theorem totalA_eq (m c : ℕ) (hc : 4 ≤ c) (hcm : c ≤ m) :
    totalA m c = 3 * m - c := by
  unfold totalA coreA coreP freeW
  omega

/-- The half appearing in `Cell` is an exact integer quotient. -/
theorem cell_half_integral (n₁ n₂ n₃ : ℕ) :
    2 ∣ ((n₁ : ℤ) + (n₂ : ℤ) + (n₃ : ℤ)) ^ 2 -
      ((n₁ : ℤ) + 3 * (n₂ : ℤ) + 5 * (n₃ : ℤ)) := by
  have he := Int.even_mul_pred_self ((n₁ : ℤ) + (n₂ : ℤ) + (n₃ : ℤ))
  rcases he with ⟨k, hk⟩
  refine ⟨k - (n₂ : ℤ) - 2 * (n₃ : ℤ), ?_⟩
  nlinarith [hk]

/-- One integral profile satisfies the desired incidence inequality. -/
def ProfileBound (m q c i n₁ n₂ n₃ : ℕ) : Prop :=
  let d := profileDim i n₁ n₂ n₃
  (q : ℤ) * (d : ℤ) + Cell m c i n₁ n₂ n₃ +
    min (((c : ℤ) + 4) * (d : ℤ)) (outerJ m q c) ≤ Phi m c i n₁ n₂ n₃

instance (m q c i n₁ n₂ n₃ : ℕ) : Decidable (ProfileBound m q c i n₁ n₂ n₃) := by
  unfold ProfileBound
  infer_instance

/-- Dependent finite indices enumerate exactly the ordered integral layer profiles. -/
def ConfigurationValid (m q c : ℕ) : Prop :=
  ∀ i : Fin (coreA c + 1), ∀ n₁ : Fin (freeW m c + 1),
  ∀ n₂ : Fin (n₁.val + 1), ∀ n₃ : Fin (n₂.val + 1),
  profileDim i n₁ n₂ n₃ ≠ 0 →
  profileDim i n₁ n₂ n₃ ≠ totalA m c →
  ProfileBound m q c i n₁ n₂ n₃

instance (m q c : ℕ) : Decidable (ConfigurationValid m q c) := by
  unfold ConfigurationValid
  infer_instance

end Quartic.ProfileCertificate
