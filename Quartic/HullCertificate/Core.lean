module

public import Quartic.ProfileCertificate.Core

@[expose] public section

/-!
# Exact arithmetic infrastructure for the weak-vertex hull certificates

The source vertices are scaled by six, avoiding rational normalization in finite
checks. This module proves the integer minimum principle and interval coverage
used by the certificates. It makes no geometric concavity assumption.
-/

namespace Quartic.HullCertificate

open Quartic.Counts Quartic.FiniteCounts Quartic.ProfileCertificate

/-- A convex integer quadratic, with its coefficients left explicit. -/
def quadratic (a b c x : ℤ) : ℤ := a * x ^ 2 + b * x + c

/-- Neighboring finite differences certify an integer minimizer on a closed interval. -/
theorem quadratic_minimum (a b c lo hi k d : ℤ) (ha : 0 ≤ a)
    (_hklo : lo ≤ k) (_hkhi : k ≤ hi)
    (hleft : k = lo ∨ a * (2 * k - 1) + b ≤ 0)
    (hright : k = hi ∨ 0 ≤ a * (2 * k + 1) + b)
    (hdlo : lo ≤ d) (hdhi : d ≤ hi) :
    quadratic a b c k ≤ quadratic a b c d := by
  have hid : quadratic a b c d - quadratic a b c k =
      (d - k) * (a * (d + k) + b) := by unfold quadratic; ring
  rcases lt_trichotomy d k with hlt | heq | hgt
  · have hl : a * (2 * k - 1) + b ≤ 0 := hleft.resolve_left (by omega)
    have ht : 0 ≤ a * (k - 1 - d) := mul_nonneg ha (by omega)
    have hc : a * (d + k) + b ≤ 0 := by nlinarith
    have hp := mul_nonneg_of_nonpos_of_nonpos (show d - k ≤ 0 by omega) hc
    linarith
  · subst d
    exact le_rfl
  · have hr : 0 ≤ a * (2 * k + 1) + b := hright.resolve_left (by omega)
    have ht : 0 ≤ a * (d - k - 1) := mul_nonneg ha (by omega)
    have hc : 0 ≤ a * (d + k) + b := by nlinarith
    have hp := mul_nonneg (show 0 ≤ d - k by omega) hc
    linarith

/-- Finite data sufficient to prove nonnegativity of a quadratic on an interval. -/
def MinimumValid (a b c lo hi k : ℤ) : Prop :=
  0 ≤ a ∧ lo ≤ k ∧ k ≤ hi ∧
  (k = lo ∨ a * (2 * k - 1) + b ≤ 0) ∧
  (k = hi ∨ 0 ≤ a * (2 * k + 1) + b) ∧
  0 ≤ quadratic a b c k

instance (a b c lo hi k : ℤ) : Decidable (MinimumValid a b c lo hi k) := by
  unfold MinimumValid
  infer_instance

theorem MinimumValid.nonnegative {a b c lo hi k : ℤ}
    (h : MinimumValid a b c lo hi k) (d : ℤ) (hdlo : lo ≤ d) (hdhi : d ≤ hi) :
    0 ≤ quadratic a b c d := by
  rcases h with ⟨ha, hklo, hkhi, hleft, hright, hk⟩
  exact le_trans hk (quadratic_minimum a b c lo hi k d ha hklo hkhi hleft hright hdlo hdhi)

/-- The five normalized core knots, multiplied by six. -/
def knot : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | _ => 6

structure Point where
  x : ℤ
  y : ℤ
  deriving DecidableEq, Repr

/-- The manuscript's weak vertex, in integer coordinates `(6ell,6I)`. -/
def baseVertex (A B w b₂ b₃ : ℤ) (sigma r : ℕ) : Point :=
  ⟨A * (sigma : ℤ) + 6 * (r : ℤ) * w,
    B * w * max (sigma : ℤ) (2 * (r : ℤ)) +
      A * b₂ * max (sigma : ℤ) (min (3 * (r : ℤ)) 6) +
      6 * (r : ℤ) * b₃⟩

/-- Two consecutive knots and four ranks yield eight vertices per cell. -/
def vertex (m c cell index : ℕ) : Point :=
  baseVertex (coreA c) (coreB c) (freeW m c)
    (quadratics (freeW m c)) (cubics (freeW m c))
    (knot (cell + index % 2)) (index / 2)

/-- Original rational source coordinate at a normalized core dimension. -/
def weakSource (A w : ℤ) (x : ℚ) (r : ℕ) : ℚ := (A : ℚ) * x + (r : ℚ) * (w : ℚ)

/-- Original weak-vertex image expression from the manuscript. -/
def weakImage (A B w b₂ b₃ : ℤ) (x : ℚ) (r : ℕ) : ℚ :=
  (B : ℚ) * (w : ℚ) * max x ((r : ℚ) / 3) +
    (A : ℚ) * (b₂ : ℚ) * max x (min ((r : ℚ) / 2) 1) + (r : ℚ) * (b₃ : ℚ)

theorem baseVertex_source (A B w b₂ b₃ : ℤ) (sigma r : ℕ) :
    ((baseVertex A B w b₂ b₃ sigma r).x : ℚ) / 6 =
      weakSource A w ((sigma : ℚ) / 6) r := by
  simp only [baseVertex, weakSource]
  push_cast
  ring

/-- The scaled formula is exactly the rational weak-image expression on all
ranks and knots used by the certificate. -/
theorem baseVertex_image (A B w b₂ b₃ : ℤ) (sigma : Fin 7) (r : Fin 4) :
    ((baseVertex A B w b₂ b₃ sigma r).y : ℚ) / 6 =
      weakImage A B w b₂ b₃ (((sigma : ℕ) : ℚ) / 6) r := by
  fin_cases sigma <;> fin_cases r <;>
    norm_num [baseVertex, weakImage] <;> ring

/-- Interval metadata is independent of its certificate payload. -/
structure Interval (α : Type) where
  lo : ℤ
  hi : ℤ
  payload : α
  deriving Repr

/-- A chain partitions exactly `[lo,hi]`, with no gaps or overlaps. -/
def checkCover {α : Type} (lo hi : ℤ) : List (Interval α) → Bool
  | [] => decide (hi < lo)
  | x :: xs => decide (x.lo = lo ∧ x.lo ≤ x.hi ∧ x.hi ≤ hi) &&
      checkCover (x.hi + 1) hi xs

theorem checkCover_covers {α : Type} (xs : List (Interval α)) (lo hi : ℤ)
    (h : checkCover lo hi xs = true) (d : ℤ) (hdlo : lo ≤ d) (hdhi : d ≤ hi) :
    ∃ x ∈ xs, x.lo ≤ d ∧ d ≤ x.hi := by
  induction xs generalizing lo with
  | nil =>
    simp only [checkCover, decide_eq_true_eq] at h
    omega
  | cons x xs ih =>
    simp only [checkCover, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨hxlo, hxvalid, hxhi⟩, htail⟩
    by_cases hdx : d ≤ x.hi
    · exact ⟨x, List.mem_cons_self, by omega, hdx⟩
    · obtain ⟨y, hy, hylo, hyhi⟩ := ih (x.hi + 1) htail (by omega)
      exact ⟨y, List.mem_cons_of_mem x hy, hylo, hyhi⟩

end Quartic.HullCertificate
