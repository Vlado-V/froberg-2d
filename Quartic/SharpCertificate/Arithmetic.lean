module

public import Quartic.SharpCertificate.Expression
public import Quartic.HullCertificate.Rational

@[expose] public section

/-! Clearing positive denominators in the two sharp incidence inequalities. -/

namespace Quartic.SharpCertificate

open Quartic.HullCertificate

/-- Cubic numerator of the outer incidence margin. -/
def outerPolynomial (s : Scalars) (D : ℤ) (f : Cubic) : Cubic :=
  ⟨f.a, f.b + D, f.c - D * (s.q + s.a), f.e⟩

/-- Cubic numerator of a sufficient normal incidence margin. -/
def normalPolynomial (s : Scalars) (D : ℤ) (f : Cubic) (first second strict : Bool) : Cubic :=
  ⟨f.a, f.b + D,
    f.c - D * (s.q + s.a + if strict then 0 else codimSlope s first second),
    f.e - D * (s.j - 1 - if strict then 0 else codimConstant s first second + target s) -
      if strict then 1 else 0⟩

theorem outerPolynomial_eval (s : Scalars) (D : ℤ) (f : Cubic) (d : ℤ) :
    (outerPolynomial s D f).eval d = f.eval d - D * d * (s.q + s.a - d) := by
  unfold outerPolynomial Cubic.eval cubic
  ring

theorem normalPolynomial_eval (s : Scalars) (D : ℤ) (f : Cubic) (d : ℤ)
    (first second strict : Bool) :
    (normalPolynomial s D f first second strict).eval d =
      if strict then f.eval d - D * (s.j - 1 + d * (s.q + s.a - d)) - 1
      else f.eval d - D * (s.j - 1 + d * (s.q + s.a - d) -
        (codimConstant s first second - codimSlope s first second * d) - target s) := by
  cases strict <;> simp only [normalPolynomial, Cubic.eval, cubic, ite_true,
    Bool.false_eq_true, ite_false] <;> ring

/-- Nonnegative integral margin numerators imply the original rational tests. -/
theorem imageBounds_of_polynomials (s : Scalars) (D : ℤ) (f : Cubic) (d : ℤ)
    (first second strict : Bool) (hD : 0 < D)
    (ho : 0 ≤ (outerPolynomial s D f).eval d)
    (hn : 0 ≤ (normalPolynomial s D f first second strict).eval d) :
    ImageBounds s ((f.eval d : ℚ) / (D : ℚ)) d := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hoq : (0 : ℚ) ≤ (f.eval d : ℚ) - (D : ℚ) * (d : ℚ) *
      ((s.q : ℚ) + (s.a : ℚ) - (d : ℚ)) := by
    rw [outerPolynomial_eval] at ho
    exact_mod_cast ho
  refine ⟨(le_div_iff₀ hDq).2 (by nlinarith only [hoq]), ?_⟩
  rw [normalPolynomial_eval] at hn
  cases strict
  · right
    simp only [Bool.false_eq_true, ite_false] at hn
    have hnq : (0 : ℚ) ≤ (f.eval d : ℚ) - (D : ℚ) *
        ((s.j : ℚ) - 1 + (d : ℚ) * ((s.q : ℚ) + (s.a : ℚ) - (d : ℚ)) -
          ((codimConstant s first second : ℚ) -
            (codimSlope s first second : ℚ) * (d : ℚ)) - (target s : ℚ)) := by
      exact_mod_cast hn
    have hbound : (s.j : ℚ) - 1 + (d : ℚ) * ((s.q : ℚ) + (s.a : ℚ) - (d : ℚ)) -
        ((codimConstant s first second : ℚ) - (codimSlope s first second : ℚ) * (d : ℚ)) -
        (target s : ℚ) ≤ (f.eval d : ℚ) / (D : ℚ) := by
      apply (le_div_iff₀ hDq).2
      nlinarith only [hnq]
    have hlow : (codimConstant s first second : ℚ) - (codimSlope s first second : ℚ) * (d : ℚ) ≤
        (codimension s d : ℚ) := by
      exact_mod_cast codimension_lower_bound s d first second
    unfold covectorBound
    nlinarith only [hbound, hlow]
  · left
    simp only [ite_true] at hn
    have hnq : (0 : ℚ) ≤ (f.eval d : ℚ) - (D : ℚ) *
        ((s.j : ℚ) - 1 + (d : ℚ) * ((s.q : ℚ) + (s.a : ℚ) - (d : ℚ))) - 1 := by
      exact_mod_cast hn
    have hbound : (s.j : ℚ) - 1 + (d : ℚ) * ((s.q : ℚ) + (s.a : ℚ) - (d : ℚ)) <
        (f.eval d : ℚ) / (D : ℚ) := by
      apply (lt_div_iff₀ hDq).2
      nlinarith only [hnq]
    unfold covectorBound
    nlinarith only [hbound]

end Quartic.SharpCertificate
