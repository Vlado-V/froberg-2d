module

public import Quartic.MarkedProfileBounds
public import Quartic.MarkedIncidence
public import Quartic.SharpMinimization.Finite

@[expose] public section

/-! Conversion of marked certificate output to the original Euler and
codimension formulas. -/

namespace Quartic.MarkedFiniteBounds

open Quartic.Counts Quartic.HullCertificate Quartic.ProfileCertificate
open Quartic.SharpMinimization Quartic.UniformScalar
open Quartic.MarkedProfileBounds

/-- The original covector test with the enlarged scalar block and the
positive parent Euler surplus minus two as target. -/
def MarkedCovectorBound (m q c : ℕ) (image : ℝ) (d : ℤ) : Prop :=
  let R := covectorR (j m q c) image q (totalA m c) d
  R < 0 ∨ R - (markedCodimension m q c d : ℝ) ≤
    (chi (m + 3) (q + c + 4) : ℝ) - 2

/-- Certificate output has exactly the stronger marked codimension and target. -/
theorem marked_covector_bound_of_imageBounds (m q c : ℕ) (image : ℝ) (d : ℤ)
    (hpos : 0 < chi (m + 3) (q + c + 4))
    (h : ImageBoundsReal (markedScalars (scalars m q c)) image d) :
    MarkedCovectorBound m q c image d := by
  obtain ⟨hj, hk, hS, ht⟩ := scalars_original_counts m q c
  have hpos' : 0 < (scalars m q c).j - (scalars m q c).total := by
    rw [hj, ht, transfer_euler_identity]
    exact hpos
  have htarget := target_markedScalars_of_pos (scalars m q c) hpos'
  rw [hj, ht, transfer_euler_identity] at htarget
  have hcod : codimension (markedScalars (scalars m q c)) d =
      markedCodimension m q c d := by
    rw [codimension_markedScalars, hk, hS]
    rfl
  have hresult := h.2
  rw [htarget, hcod] at hresult
  simpa only [MarkedCovectorBound, markedScalars_j, markedScalars_q,
    markedScalars_a, hj, show (scalars m q c).q = (q : ℤ) from rfl,
    show (scalars m q c).a = (totalA m c : ℤ) from rfl,
    Int.cast_sub, Int.cast_ofNat, Int.cast_natCast] using hresult

/-- A sharper image lower bound preserves the marked covector test. -/
theorem MarkedCovectorBound.mono {m q c : ℕ} {image image' : ℝ} {d : ℤ}
    (h : MarkedCovectorBound m q c image d) (hi : image ≤ image') :
    MarkedCovectorBound m q c image' d := by
  have hR : covectorR (j m q c) image' q (totalA m c) d ≤
      covectorR (j m q c) image q (totalA m c) d := by
    unfold covectorR
    linarith
  rcases h with hnegative | hnormal
  · exact Or.inl (hR.trans_lt hnegative)
  · right
    linarith

end Quartic.MarkedFiniteBounds
