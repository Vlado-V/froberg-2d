module

public import Quartic.HullCertificate.Rational

@[expose] public section

/-! The scalar incidence data after adjoining one marked coefficient. -/

namespace Quartic.HullCertificate

/-- Adjoining a marked coefficient increases the scalar parameter block and
the total parameter dimension by one. -/
def markedScalars (s : Scalars) : Scalars :=
  { s with S := s.S + 1, total := s.total + 1 }

@[simp] theorem markedScalars_a (s : Scalars) : (markedScalars s).a = s.a := rfl
@[simp] theorem markedScalars_q (s : Scalars) : (markedScalars s).q = s.q := rfl
@[simp] theorem markedScalars_c (s : Scalars) : (markedScalars s).c = s.c := rfl
@[simp] theorem markedScalars_j (s : Scalars) : (markedScalars s).j = s.j := rfl
@[simp] theorem markedScalars_k (s : Scalars) : (markedScalars s).k = s.k := rfl
@[simp] theorem markedScalars_S (s : Scalars) : (markedScalars s).S = s.S + 1 := rfl
@[simp] theorem markedScalars_total (s : Scalars) :
    (markedScalars s).total = s.total + 1 := rfl

theorem target_markedScalars (s : Scalars) :
    target (markedScalars s) = max (s.j - s.total - 1) 0 - 1 := by
  change max (s.j - (s.total + 1)) 0 - 1 = max (s.j - s.total - 1) 0 - 1
  congr 2 <;> omega

/-- A positive unmarked surplus loses one dimension when a coefficient is
marked, so the incidence target is the unmarked surplus minus two. -/
theorem target_markedScalars_of_pos (s : Scalars) (hs : 0 < s.j - s.total) :
    target (markedScalars s) = s.j - s.total - 2 := by
  rw [target_markedScalars]
  omega

theorem target_markedScalars_of_nonpos (s : Scalars) (hs : s.j - s.total ≤ 0) :
    target (markedScalars s) = -1 := by
  rw [target_markedScalars]
  omega

@[simp] theorem covectorBound_markedScalars (s : Scalars) (image : ℚ) (d : ℤ) :
    covectorBound (markedScalars s) image d = covectorBound s image d := rfl

theorem codimension_markedScalars (s : Scalars) (d : ℤ) :
    codimension (markedScalars s) d =
      max (s.k - 4 * d) 0 + max (s.S + 1 - s.c * d) 0 := rfl

theorem codimension_le_markedScalars (s : Scalars) (d : ℤ) :
    codimension s d ≤ codimension (markedScalars s) d := by
  simp only [codimension, markedScalars]
  omega

theorem codimension_markedScalars_le (s : Scalars) (d : ℤ) :
    codimension (markedScalars s) d ≤ codimension s d + 1 := by
  simp only [codimension, markedScalars]
  omega

theorem codimension_markedScalars_of_nonneg (s : Scalars) (d : ℤ)
    (hs : 0 ≤ s.S - s.c * d) :
    codimension (markedScalars s) d = codimension s d + 1 := by
  simp only [codimension, markedScalars]
  omega

theorem codimension_markedScalars_of_neg (s : Scalars) (d : ℤ)
    (hs : s.S - s.c * d < 0) :
    codimension (markedScalars s) d = codimension s d := by
  simp only [codimension, markedScalars]
  omega

/-- The marked incidence statement uses the same covector expression, the
enlarged coefficient codimension, and the surplus-minus-two target. -/
theorem imageBounds_markedScalars_iff_of_pos (s : Scalars) (image : ℚ) (d : ℤ)
    (hs : 0 < s.j - s.total) :
    ImageBounds (markedScalars s) image d ↔
      (d : ℚ) * ((s.q : ℚ) + (s.a : ℚ) - (d : ℚ)) ≤ image ∧
        (covectorBound s image d < 0 ∨
          covectorBound s image d - (codimension (markedScalars s) d : ℚ) ≤
            (s.j : ℚ) - (s.total : ℚ) - 2) := by
  simp only [ImageBounds, markedScalars_q, markedScalars_a,
    covectorBound_markedScalars, target_markedScalars_of_pos s hs, Int.cast_sub,
    Int.cast_ofNat]

end Quartic.HullCertificate
