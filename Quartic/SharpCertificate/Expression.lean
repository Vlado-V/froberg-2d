import Quartic.SharpCertificate.Bernstein

/-! Exact source formulas for the rational sharp edges. -/

namespace Quartic.SharpCertificate

open Quartic.Counts Quartic.FiniteCounts Quartic.ProfileCertificate

/-- The manuscript's sharp core shadow `B - choose(p-ceil(i/2)+1,2)`. -/
def coreShadow (c i : ℕ) : ℤ :=
  coreB c - quadratics (coreP c - (i + 1) / 2)

/-- Polynomial evaluation agrees with the original binomial shadow count. -/
theorem coreShadow_eq_binomial (c i : ℕ) :
    coreShadow c i = coreB c - (((coreP c - (i + 1) / 2 + 1).choose 2 : ℕ) : ℤ) := by
  simp only [coreShadow, quadratics_eq_b2, b2]

structure Parameters where
  w : ℤ
  i : ℤ
  B : ℤ
  shadow : ℤ
  b₂ : ℤ
  b₃ : ℤ
  e₁ : ℤ
  e₂ : ℤ
  deriving Repr

/-- Coefficients of `sc:sharp-expression`, with original dimension counts. -/
def parameters (m c i : ℕ) : Parameters :=
  ⟨freeW m c, i, coreB c, coreShadow c i,
    quadratics (freeW m c), cubics (freeW m c),
    max ((coreP c : ℤ) - (i : ℤ)) 0,
    (coreA c : ℤ) - max (i : ℤ) (coreP c : ℤ)⟩

/-- The polynomial extension of the free quadratic monomial count. -/
def H₂ (w : ℤ) (x : ℚ) : ℚ :=
  ((w : ℚ) * ((w : ℚ) + 1) - ((w : ℚ) - x) * ((w : ℚ) - x + 1)) / 2

/-- The polynomial extension of the free cubic monomial count. -/
def H₃ (w : ℤ) (x : ℚ) : ℚ :=
  ((w : ℚ) * ((w : ℚ) + 1) * ((w : ℚ) + 2) -
    ((w : ℚ) - x) * ((w : ℚ) - x + 1) * ((w : ℚ) - x + 2)) / 6

/-- The original rational sharp profile expression. -/
def sharpProfile (p : Parameters) (n₁ n₂ n₃ : ℚ) : ℚ :=
  (p.shadow : ℚ) * (p.w : ℚ) + ((p.B : ℚ) - (p.shadow : ℚ)) * n₁ +
    (p.i : ℚ) * (p.b₂ : ℚ) + (p.e₁ : ℚ) * H₂ p.w n₁ +
    (p.e₂ : ℚ) * H₂ p.w n₂ + H₃ p.w n₁ + H₃ p.w n₂ + H₃ p.w n₃

/-- The six edges `(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)`. -/
def edgeLeft (edge : Fin 6) : ℕ :=
  match edge.val with | 0 | 1 | 2 => 0 | 3 | 4 => 1 | _ => 2

def edgeRight (edge : Fin 6) : ℕ :=
  match edge.val with | 0 => 1 | 1 | 3 => 2 | _ => 3

def edgeWidth (edge : Fin 6) : ℤ := (edgeRight edge - edgeLeft edge : ℕ)
def edgeScale (edge : Fin 6) : ℤ := 6 * edgeWidth edge ^ 3

theorem edgeWidth_pos (edge : Fin 6) : 0 < edgeWidth edge := by
  fin_cases edge <;> decide

theorem edgeScale_pos (edge : Fin 6) : 0 < edgeScale edge := by
  unfold edgeScale
  have h := edgeWidth_pos edge
  positivity

/-- The displayed intermediate layer value in `sc:edge`. -/
def edgeIntermediate (p : Parameters) (edge : Fin 6) (d : ℤ) : ℚ :=
  ((d : ℚ) - (p.i : ℚ) - (edgeLeft edge : ℚ) * (p.w : ℚ)) / (edgeWidth edge : ℚ)

/-- Layer `h` of a point on a prefix edge. -/
def edgeLayer (w : ℤ) (z : ℚ) (left right h : ℕ) : ℚ :=
  if h ≤ left then (w : ℚ) else if h ≤ right then z else 0

def sharpEdge (p : Parameters) (edge : Fin 6) (d : ℤ) : ℚ :=
  let z := edgeIntermediate p edge d
  sharpProfile p (edgeLayer p.w z (edgeLeft edge) (edgeRight edge) 1)
    (edgeLayer p.w z (edgeLeft edge) (edgeRight edge) 2)
    (edgeLayer p.w z (edgeLeft edge) (edgeRight edge) 3)

def prefixCoefficient (p : Parameters) (r : ℕ) : ℤ :=
  (if 0 < r then p.e₁ else 0) + (if 1 < r then p.e₂ else 0)

/-- Integer cubic equal to `6(v-u)^3` times the sharp rational edge value. -/
def edgePolynomial (p : Parameters) (edge : Fin 6) : Cubic :=
  let K := edgeWidth edge
  let D := edgeScale edge
  let L := p.i + (edgeRight edge : ℤ) * p.w
  let e := prefixCoefficient p (edgeRight edge) - prefixCoefficient p (edgeLeft edge)
  let Q := p.B - p.shadow
  let C := p.shadow * p.w + p.i * p.b₂ +
    p.b₂ * prefixCoefficient p (edgeRight edge) + (edgeRight edge : ℤ) * p.b₃
  ⟨K, -3 * K * e - 3 * K * (L + K),
    (if edgeLeft edge = 0 then 6 * K^2 * Q else 0) +
      3 * K * e * (2 * L + K) + K * (L * (L + K) + L * (L + 2*K) + (L + K) * (L + 2*K)),
    D * C + (if edgeLeft edge = 0 then -6 * K^2 * Q * p.i else D * Q * p.w) -
      3 * K * e * L * (L + K) - K * L * (L + K) * (L + 2*K)⟩

/-- Algebraic equality connecting the checked integer cubic to the original
rational edge expression. It holds for every integral source dimension. -/
theorem edgePolynomial_eq_scaled (p : Parameters) (edge : Fin 6) (d : ℤ)
    (hb₂ : 2 * p.b₂ = p.w * (p.w + 1))
    (hb₃ : 6 * p.b₃ = p.w * (p.w + 1) * (p.w + 2)) :
    ((edgePolynomial p edge).eval d : ℚ) = (edgeScale edge : ℚ) * sharpEdge p edge d := by
  have hb₂q : (p.b₂ : ℚ) = (p.w : ℚ) * ((p.w : ℚ) + 1) / 2 := by
    have h : 2 * (p.b₂ : ℚ) = (p.w : ℚ) * ((p.w : ℚ) + 1) := by exact_mod_cast hb₂
    linarith
  have hb₃q : (p.b₃ : ℚ) = (p.w : ℚ) * ((p.w : ℚ) + 1) * ((p.w : ℚ) + 2) / 6 := by
    have h : 6 * (p.b₃ : ℚ) = (p.w : ℚ) * ((p.w : ℚ) + 1) * ((p.w : ℚ) + 2) := by
      exact_mod_cast hb₃
    linarith
  fin_cases edge <;>
    norm_num [edgePolynomial, Cubic.eval, cubic, edgeScale, edgeWidth, edgeLeft, edgeRight,
      prefixCoefficient, sharpEdge, sharpProfile, edgeLayer, edgeIntermediate, H₂, H₃] <;>
    rw [hb₂q, hb₃q] <;> ring

theorem parameters_b₂_scaled (m c i : ℕ) :
    2 * (parameters m c i).b₂ = (parameters m c i).w * ((parameters m c i).w + 1) := by
  simpa only [parameters, quadratics_eq_b2] using b2_scaled (freeW m c)

theorem parameters_b₃_scaled (m c i : ℕ) :
    6 * (parameters m c i).b₃ = (parameters m c i).w *
      ((parameters m c i).w + 1) * ((parameters m c i).w + 2) := by
  simpa only [parameters, cubics_eq_b3] using b3_scaled (freeW m c)

/-- The rational sharp value is exactly the quotient used by the certificates. -/
theorem sharpEdge_eq_quotient (m c i : ℕ) (edge : Fin 6) (d : ℤ) :
    sharpEdge (parameters m c i) edge d =
      ((edgePolynomial (parameters m c i) edge).eval d : ℚ) / (edgeScale edge : ℚ) := by
  have hD : (edgeScale edge : ℚ) ≠ 0 := by
    have h : (0 : ℚ) < edgeScale edge := by exact_mod_cast edgeScale_pos edge
    exact ne_of_gt h
  symm
  apply (div_eq_iff hD).2
  rw [edgePolynomial_eq_scaled _ _ _ (parameters_b₂_scaled m c i) (parameters_b₃_scaled m c i)]
  ring

end Quartic.SharpCertificate
