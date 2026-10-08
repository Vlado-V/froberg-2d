import Quartic.HullCertificate.Certificate

/-! Exact integer cubic positivity certificates. -/

namespace Quartic.SharpCertificate

def cubic (a b c e x : ℤ) : ℤ := ((a * x + b) * x + c) * x + e

def B₀ (a b c e lo : ℤ) : ℤ := 3 * cubic a b c e lo
def B₁ (a b c e lo hi : ℤ) : ℤ :=
  3 * cubic a b c e lo + ((3 * a * lo + 2 * b) * lo + c) * (hi - lo)
def B₂ (a b c e lo hi : ℤ) : ℤ :=
  3 * cubic a b c e lo + 2 * ((3 * a * lo + 2 * b) * lo + c) * (hi - lo) +
    (3 * a * lo + b) * (hi - lo) ^ 2

theorem cubic_nonnegative (a b c e lo hi x : ℤ)
    (hxlo : lo ≤ x) (hxhi : x ≤ hi)
    (h₀ : 0 ≤ B₀ a b c e lo)
    (h₁ : 0 ≤ B₁ a b c e lo hi)
    (h₂ : 0 ≤ B₂ a b c e lo hi)
    (h₃ : 0 ≤ cubic a b c e hi) :
    0 ≤ cubic a b c e x := by
  by_cases heq : lo = hi
  · have hx : x = hi := by omega
    simpa only [hx] using h₃
  have hwidth : 0 < hi - lo := by omega
  have hleft : 0 ≤ x - lo := by omega
  have hright : 0 ≤ hi - x := by omega
  have hid : 3 * (hi - lo)^3 * cubic a b c e x =
      B₀ a b c e lo * (hi - x)^3 +
      3 * B₁ a b c e lo hi * (x - lo) * (hi - x)^2 +
      3 * B₂ a b c e lo hi * (x - lo)^2 * (hi - x) +
      3 * cubic a b c e hi * (x - lo)^3 := by
    unfold B₀ B₁ B₂ cubic
    ring
  have hprod : 0 ≤ 3 * (hi - lo)^3 * cubic a b c e x := by
    rw [hid]
    positivity
  have hfactor : 0 < 3 * (hi - lo)^3 := by positivity
  exact nonneg_of_mul_nonneg_right hprod hfactor

/-- Coefficients of an integral cubic polynomial. -/
structure Cubic where
  a : ℤ
  b : ℤ
  c : ℤ
  e : ℤ
  deriving Repr

def Cubic.eval (f : Cubic) (x : ℤ) : ℤ := cubic f.a f.b f.c f.e x

/-- Four Bernstein coefficients certify nonnegativity on an interval. -/
def Cubic.Valid (f : Cubic) (lo hi : ℤ) : Prop :=
  0 ≤ B₀ f.a f.b f.c f.e lo ∧
  0 ≤ B₁ f.a f.b f.c f.e lo hi ∧
  0 ≤ B₂ f.a f.b f.c f.e lo hi ∧
  0 ≤ f.eval hi

instance (f : Cubic) (lo hi : ℤ) : Decidable (f.Valid lo hi) := by
  unfold Cubic.Valid
  infer_instance

theorem Cubic.Valid.nonnegative {f : Cubic} {lo hi : ℤ} (h : f.Valid lo hi)
    (x : ℤ) (hxlo : lo ≤ x) (hxhi : x ≤ hi) : 0 ≤ f.eval x := by
  exact cubic_nonnegative _ _ _ _ _ _ _ hxlo hxhi h.1 h.2.1 h.2.2.1 h.2.2.2

end Quartic.SharpCertificate
