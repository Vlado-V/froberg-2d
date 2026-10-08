import Quartic.HullCertificate.Core

/-! Supporting-line certificates and their connection to the two incidence tests. -/

namespace Quartic.HullCertificate

open Quartic.Counts Quartic.FiniteCounts Quartic.ProfileCertificate

structure Line where
  denominator : ℤ
  slope : ℤ
  intercept : ℤ
  deriving DecidableEq, Repr

/-- The affine line through two scaled weak vertices. -/
def lineBetween (p q : Point) : Line :=
  ⟨6 * (q.x - p.x), 6 * (q.y - p.y), p.y * (q.x - p.x) - p.x * (q.y - p.y)⟩

/-- Evaluation at the unscaled source dimension. -/
def Line.value (l : Line) (x : ℚ) : ℚ :=
  ((l.slope : ℚ) * x + (l.intercept : ℚ)) / (l.denominator : ℚ)

/-- Integer form of lying below the scaled point `(6ell,6I)`. -/
def Supports (l : Line) (v : Point) : Prop :=
  l.slope * v.x + 6 * l.intercept ≤ l.denominator * v.y

instance (l : Line) (v : Point) : Decidable (Supports l v) := by
  unfold Supports
  infer_instance

theorem Supports.rational_bound {l : Line} {v : Point}
    (hden : 0 < l.denominator) (h : Supports l v) :
    l.value ((v.x : ℚ) / 6) ≤ (v.y : ℚ) / 6 := by
  have hd : (0 : ℚ) < l.denominator := by exact_mod_cast hden
  unfold Line.value
  apply (div_le_iff₀ hd).2
  have hc : (l.slope : ℚ) * (v.x : ℚ) + 6 * (l.intercept : ℚ) ≤
      (l.denominator : ℚ) * (v.y : ℚ) := by exact_mod_cast h
  nlinarith only [hc]

structure Scalars where
  a : ℤ
  q : ℤ
  c : ℤ
  j : ℤ
  k : ℤ
  S : ℤ
  total : ℤ
  deriving Repr

/-- Original dimension formulas, evaluated by their proved polynomial forms. -/
def scalars (m q c : ℕ) : Scalars :=
  let α := quadratics m - (q : ℤ)
  let h := 3 * (m : ℤ) * (c : ℤ) - 2 * α - pairs c
  let k := 2 * (m : ℤ) + 2 * (c : ℤ)
  let δ := -euler m q
  ⟨totalA m c, q, c, outerJ m q c, k, h + 3 + δ, h + k + 3 + δ⟩

/-- The computed scalar fields are the original manuscript dimension counts. -/
theorem scalars_original_counts (m q c : ℕ) :
    (scalars m q c).j = j m q c ∧
    (scalars m q c).k = k31 m c ∧
    (scalars m q c).S = H m q c + 3 + delta m q ∧
    (scalars m q c).total = hTotal m q c := by
  simp [scalars, outerJ_eq_j, quadratics_eq_b2, pairs_eq_choose,
    euler_eq_chi, k31, H, delta, hTotal, alpha]

/-- Coefficient codimension `C(d)` from the manuscript. -/
def codimension (s : Scalars) (d : ℤ) : ℤ :=
  max (s.k - 4 * d) 0 + max (s.S - s.c * d) 0

def target (s : Scalars) : ℤ := max (s.j - s.total) 0 - 1

def covectorBound (s : Scalars) (image : ℚ) (d : ℤ) : ℚ :=
  (s.j : ℚ) - image + (s.q : ℚ) * (d : ℚ) +
    (d : ℚ) * ((s.a : ℚ) - (d : ℚ)) - 1

/-- Either affine summand may be retained as a lower bound for its maximum. -/
def codimConstant (s : Scalars) (first second : Bool) : ℤ :=
  (if first then s.k else 0) + (if second then s.S else 0)

def codimSlope (s : Scalars) (first second : Bool) : ℤ :=
  (if first then 4 else 0) + (if second then s.c else 0)

theorem codimension_lower_bound (s : Scalars) (d : ℤ) (first second : Bool) :
    codimConstant s first second - codimSlope s first second * d ≤ codimension s d := by
  have h₁ := le_max_left (s.k - 4 * d) 0
  have h₂ := le_max_right (s.k - 4 * d) 0
  have h₃ := le_max_left (s.S - s.c * d) 0
  have h₄ := le_max_right (s.S - s.c * d) 0
  cases first <;> cases second <;>
    simp only [codimConstant, codimSlope, Bool.false_eq_true, ite_false, ite_true, codimension] <;>
    nlinarith

/-- Coefficients of the outer quadratic after clearing the positive denominator. -/
def outerLinear (s : Scalars) (l : Line) : ℤ := l.slope - l.denominator * (s.q + s.a)

def normalLinear (s : Scalars) (l : Line) (first second strict : Bool) : ℤ :=
  if strict then outerLinear s l
  else l.slope - l.denominator * (s.q + s.a + codimSlope s first second)

def normalConstant (s : Scalars) (l : Line) (first second strict : Bool) : ℤ :=
  if strict then l.intercept - l.denominator * (s.j - 1) - 1
  else l.intercept - l.denominator * (s.j - 1 - codimConstant s first second - target s)

theorem outer_of_quadratic (s : Scalars) (l : Line) (d : ℤ)
    (hden : 0 < l.denominator)
    (h : 0 ≤ quadratic l.denominator (outerLinear s l) l.intercept d) :
    (d : ℚ) * ((s.q : ℚ) + (s.a : ℚ) - (d : ℚ)) ≤ l.value d := by
  have hd : (0 : ℚ) < l.denominator := by exact_mod_cast hden
  unfold Line.value
  apply (le_div_iff₀ hd).2
  have hc : (0 : ℚ) ≤ (quadratic l.denominator (outerLinear s l) l.intercept d : ℤ) :=
    by exact_mod_cast h
  unfold quadratic outerLinear at hc
  push_cast at hc
  nlinarith only [hc]

theorem normal_of_quadratic (s : Scalars) (l : Line) (d : ℤ)
    (first second strict : Bool) (hden : 0 < l.denominator)
    (h : 0 ≤ quadratic l.denominator (normalLinear s l first second strict)
      (normalConstant s l first second strict) d) :
    covectorBound s (l.value d) d < 0 ∨
      covectorBound s (l.value d) d - (codimension s d : ℚ) ≤ (target s : ℚ) := by
  have hd : (0 : ℚ) < l.denominator := by exact_mod_cast hden
  have hc : (0 : ℚ) ≤
      (quadratic l.denominator (normalLinear s l first second strict)
        (normalConstant s l first second strict) d : ℤ) := by exact_mod_cast h
  cases strict
  · right
    have hlow := codimension_lower_bound s d first second
    have hlow' : (codimConstant s first second : ℚ) -
        (codimSlope s first second : ℚ) * (d : ℚ) ≤ (codimension s d : ℚ) := by
      exact_mod_cast hlow
    have hline : (s.j : ℚ) + (s.q : ℚ) * (d : ℚ) +
        (d : ℚ) * ((s.a : ℚ) - (d : ℚ)) - 1 -
        ((codimConstant s first second : ℚ) - (codimSlope s first second : ℚ) * (d : ℚ)) -
        (target s : ℚ) ≤ l.value d := by
      unfold Line.value
      apply (le_div_iff₀ hd).2
      simp only [quadratic, normalLinear, normalConstant, Bool.false_eq_true, ite_false] at hc
      push_cast at hc
      nlinarith only [hc]
    unfold covectorBound
    linarith
  · left
    have hline : (s.j : ℚ) + (s.q : ℚ) * (d : ℚ) +
        (d : ℚ) * ((s.a : ℚ) - (d : ℚ)) - 1 < l.value d := by
      unfold Line.value
      apply (lt_div_iff₀ hd).2
      simp only [quadratic, normalLinear, normalConstant, ite_true, outerLinear] at hc
      push_cast at hc
      nlinarith only [hc]
    unfold covectorBound
    linarith

end Quartic.HullCertificate
