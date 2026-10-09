module

public import Quartic.HullCertificate.Certificate

@[expose] public section

/-! The integer certificate vertices and lines agree with the original rational formulas. -/

namespace Quartic.HullCertificate

open Quartic.Counts Quartic.FiniteCounts Quartic.ProfileCertificate

theorem knot_lt_seven (k : ℕ) : knot k < 7 := by
  rcases k with _ | _ | _ | _ | k <;> norm_num [knot]

theorem vertex_source (m c cell index : ℕ) :
    ((vertex m c cell index).x : ℚ) / 6 =
      weakSource (coreA c) (freeW m c)
        ((knot (cell + index % 2) : ℚ) / 6) (index / 2) := by
  exact baseVertex_source _ _ _ _ _ _ _

/-- The scaled image coordinate is exactly `I(x,r₀)` in `sc:weak-vertex`,
with the original binomial quadratic and cubic counts. -/
theorem vertex_image (m c cell : ℕ) (index : Fin 8) :
    ((vertex m c cell index).y : ℚ) / 6 =
      weakImage (coreA c) (coreB c) (freeW m c)
        (b2 (freeW m c)) (b3 (freeW m c))
        ((knot (cell + index.val % 2) : ℚ) / 6) (index.val / 2) := by
  have h := baseVertex_image (coreA c) (coreB c) (freeW m c)
    (quadratics (freeW m c)) (cubics (freeW m c))
    ⟨knot (cell + index.val % 2), knot_lt_seven _⟩
    ⟨index.val / 2, by omega⟩
  simpa only [vertex, quadratics_eq_b2, cubics_eq_b3] using h

/-- Each certified line lies below all eight original rational weak vertices. -/
theorem LineValid.supports_weakImage {m c cell left right : ℕ}
    (h : LineValid m c cell left right) (v : Fin 8) :
    (lineBetween (vertex m c cell left) (vertex m c cell right)).value
        (weakSource (coreA c) (freeW m c)
          ((knot (cell + v.val % 2) : ℚ) / 6) (v.val / 2)) ≤
      weakImage (coreA c) (coreB c) (freeW m c)
        (b2 (freeW m c)) (b3 (freeW m c))
        ((knot (cell + v.val % 2) : ℚ) / 6) (v.val / 2) := by
  have hs := Supports.rational_bound h.2.2.1 (h.2.2.2 v)
  rw [vertex_source, vertex_image] at hs
  exact hs

/-- An explicit convex combination of the eight weak vertices. -/
def InVertexHull (m c cell : ℕ) (source image : ℚ) : Prop :=
  ∃ weight : Fin 8 → ℚ, (∀ v, 0 ≤ weight v) ∧
    (∑ v, weight v) = 1 ∧
    (∑ v, weight v * ((vertex m c cell v).x : ℚ) / 6) = source ∧
    (∑ v, weight v * ((vertex m c cell v).y : ℚ) / 6) = image

/-- Evaluation of an affine line preserves normalized weighted sums. -/
theorem Line.affine_sum (l : Line) (weight X : Fin 8 → ℚ)
    (hweight : (∑ v, weight v) = 1) :
    l.value (∑ v, weight v * X v) = ∑ v, weight v * l.value (X v) := by
  symm
  calc
    ∑ v, weight v * l.value (X v) =
        ((l.slope : ℚ) * (∑ v, weight v * X v) +
          (l.intercept : ℚ) * (∑ v, weight v)) / (l.denominator : ℚ) := by
      unfold Line.value
      simp only [← mul_div_assoc, ← Finset.sum_div]
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = l.value (∑ v, weight v * X v) := by
      rw [hweight]
      simp only [mul_one, Line.value]

/-- Supporting all vertices implies supporting every convex combination,
including every point on the lower boundary of their convex hull. -/
theorem LineValid.supports_hull {m c cell left right : ℕ}
    (h : LineValid m c cell left right) {source image : ℚ}
    (hpoint : InVertexHull m c cell source image) :
    (lineBetween (vertex m c cell left) (vertex m c cell right)).value source ≤ image := by
  obtain ⟨weight, hnonneg, hweight, hsource, himage⟩ := hpoint
  rw [← hsource, ← himage]
  simp only [mul_div_assoc]
  rw [Line.affine_sum _ _ _ hweight]
  apply Finset.sum_le_sum
  intro v _
  exact mul_le_mul_of_nonneg_left
    (Supports.rational_bound h.2.2.1 (h.2.2.2 v)) (hnonneg v)

/-- The two scalar incidence tests for any rational image estimate. -/
def ImageBounds (s : Scalars) (image : ℚ) (d : ℤ) : Prop :=
  (d : ℚ) * ((s.q : ℚ) + (s.a : ℚ) - (d : ℚ)) ≤ image ∧
    (covectorBound s image d < 0 ∨
      covectorBound s image d - (codimension s d : ℚ) ≤ (target s : ℚ))

/-- Raising an image lower bound preserves both incidence conclusions. -/
theorem IncidenceBounds.mono {s : Scalars} {l : Line} {d : ℤ}
    (h : IncidenceBounds s l d) {image : ℚ} (himage : l.value d ≤ image) :
    ImageBounds s image d := by
  refine ⟨le_trans h.1 himage, ?_⟩
  have hcov : covectorBound s image d ≤ covectorBound s (l.value d) d := by
    unfold covectorBound
    linarith
  rcases h.2 with hnegative | hnormal
  · exact Or.inl (lt_of_le_of_lt hcov hnegative)
  · right
    linarith

/-- Once a cell is certified, both incidence bounds hold for every rational
point of its vertex hull at any eligible integral source dimension. -/
theorem CellBounds.on_hull {m q c cell : ℕ} (h : CellBounds m q c cell)
    (d : ℤ) (hd : Eligible m c cell d) (image : ℚ)
    (hpoint : InVertexHull m c cell d image) :
    ImageBounds (scalars m q c) image d := by
  obtain ⟨left, right, hline, hinc⟩ := h d hd
  exact hinc.mono (hline.supports_hull hpoint)

end Quartic.HullCertificate
