module

public import Quartic.ProfileCertificate

@[expose] public section

/-! The integral profile estimate already contains the additional unit needed
when one scalar coefficient is marked. No additional finite profile search is
needed: the two codimension maxima dominate their sum. -/

namespace Quartic.MarkedProfileBounds

open Quartic.Counts Quartic.FiniteCounts Quartic.ProfileCertificate

/-- The scalar codimension after adjoining a marked coefficient. -/
def markedCodimension (m q c : ℕ) (d : ℤ) : ℤ :=
  max (k31 m c - 4 * d) 0 +
    max (H m q c + 3 + delta m q + 1 - (c : ℤ) * d) 0

/-- Algebraic form of the marked profile estimate. -/
theorem marked_bound_of_profile (q c d j k S cell image : ℤ)
    (h : q * d + cell + min ((c + 4) * d) j ≤ image) :
    j - image + q * d + cell - 1 < 0 ∨
      j - image + q * d + cell - 1 -
        (max (k - 4 * d) 0 + max (S + 1 - c * d) 0) ≤ j - (k + S) - 2 := by
  by_cases hj : j ≤ (c + 4) * d
  · rw [min_eq_right hj] at h
    left
    omega
  · rw [min_eq_left (le_of_lt (lt_of_not_ge hj))] at h
    right
    have hc := add_le_add (le_max_left (k - 4 * d) 0)
      (le_max_left (S + 1 - c * d) 0)
    nlinarith

/-- The lower configurations in dimensions 28 through 40 satisfy the marked
covector test with target equal to the parent Euler surplus minus two. -/
theorem profile_marked_inequality (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40)
    (i n₁ n₂ n₃ : ℕ)
    (hi : i ≤ coreA (mixedCount m false))
    (hn₁ : n₁ ≤ freeW m (mixedCount m false))
    (hn₂ : n₂ ≤ n₁) (hn₃ : n₃ ≤ n₂)
    (hdlo : 0 < profileDim i n₁ n₂ n₃)
    (hdhi : profileDim i n₁ n₂ n₃ < totalA m (mixedCount m false)) :
    let q := upperEndpoint m
    let c := mixedCount m false
    let d : ℤ := profileDim i n₁ n₂ n₃
    let R := j m q c - Phi m c i n₁ n₂ n₃ + q * d + Cell m c i n₁ n₂ n₃ - 1
    R < 0 ∨ R - markedCodimension m q c d ≤ j m q c - hTotal m q c - 2 := by
  have h := profile_inequality m hmlo hmhi false i n₁ n₂ n₃ hi hn₁ hn₂ hn₃ hdlo hdhi
  have hh := marked_bound_of_profile (upperEndpoint m) (mixedCount m false)
    (profileDim i n₁ n₂ n₃) (j m (upperEndpoint m) (mixedCount m false))
    (k31 m (mixedCount m false))
    (H m (upperEndpoint m) (mixedCount m false) + 3 +
      delta m (upperEndpoint m))
    (Cell m (mixedCount m false) i n₁ n₂ n₃)
    (Phi m (mixedCount m false) i n₁ n₂ n₃) h
  dsimp only
  convert hh using 1 <;> unfold markedCodimension hTotal <;> ring

end Quartic.MarkedProfileBounds
