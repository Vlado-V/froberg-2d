module

public import Quartic.HullCertificate.Arithmetic

@[expose] public section

/-! A small certificate format for supporting lines and quadratic minima. -/

namespace Quartic.HullCertificate

open Quartic.ProfileCertificate

structure Payload where
  left : ℕ
  right : ℕ
  first : Bool
  second : Bool
  strict : Bool
  outerMinimum : ℤ
  normalMinimum : ℤ
  deriving Repr

abbrev Chunk := Interval Payload

def chunkLine (m c cell : ℕ) (z : Chunk) : Line :=
  lineBetween (vertex m c cell z.payload.left) (vertex m c cell z.payload.right)

def LineValid (m c cell left right : ℕ) : Prop :=
  let l := lineBetween (vertex m c cell left) (vertex m c cell right)
  left < 8 ∧ right < 8 ∧ 0 < l.denominator ∧
    ∀ v : Fin 8, Supports l (vertex m c cell v)

instance (m c cell left right : ℕ) : Decidable (LineValid m c cell left right) := by
  unfold LineValid
  infer_instance

def ChunkValid (m q c cell : ℕ) (z : Chunk) : Prop :=
  let l := chunkLine m c cell z
  let s := scalars m q c
  LineValid m c cell z.payload.left z.payload.right ∧
    MinimumValid l.denominator (outerLinear s l) l.intercept z.lo z.hi z.payload.outerMinimum ∧
    MinimumValid l.denominator
      (normalLinear s l z.payload.first z.payload.second z.payload.strict)
      (normalConstant s l z.payload.first z.payload.second z.payload.strict)
      z.lo z.hi z.payload.normalMinimum

instance (m q c cell : ℕ) (z : Chunk) : Decidable (ChunkValid m q c cell z) := by
  unfold ChunkValid
  infer_instance

/-- Source-coordinate extremes for one of the four knot intervals, scaled by six. -/
def sourceLower (_m c cell : ℕ) : ℤ := (coreA c : ℤ) * (knot cell : ℤ)
def sourceUpper (m c cell : ℕ) : ℤ :=
  (coreA c : ℤ) * (knot (cell + 1) : ℤ) + 18 * (freeW m c : ℤ)

def dimensionLower (m c cell : ℕ) : ℤ := max 1 ((sourceLower m c cell + 5) / 6)
def dimensionUpper (m c cell : ℕ) : ℤ :=
  min ((totalA m c : ℤ) - 1) (sourceUpper m c cell / 6)

/-- A nontrivial integer source dimension is feasible in this knot interval. -/
def Eligible (m c cell : ℕ) (d : ℤ) : Prop :=
  1 ≤ d ∧ d < (totalA m c : ℤ) ∧
    sourceLower m c cell ≤ 6 * d ∧ 6 * d ≤ sourceUpper m c cell

theorem Eligible.in_range {m c cell : ℕ} {d : ℤ} (h : Eligible m c cell d) :
    dimensionLower m c cell ≤ d ∧ d ≤ dimensionUpper m c cell := by
  unfold Eligible at h
  unfold dimensionLower dimensionUpper
  omega

/-- The actual finite certificate checker. All arithmetic is integral. -/
def checkCell (m q c cell : ℕ) (xs : List Chunk) : Bool :=
  checkCover (dimensionLower m c cell) (dimensionUpper m c cell) xs &&
    xs.all fun z => decide (ChunkValid m q c cell z)

/-- Both source incidence tests for an explicitly supported affine bound. -/
def IncidenceBounds (s : Scalars) (l : Line) (d : ℤ) : Prop :=
  (d : ℚ) * ((s.q : ℚ) + (s.a : ℚ) - (d : ℚ)) ≤ l.value d ∧
    (covectorBound s (l.value d) d < 0 ∨
      covectorBound s (l.value d) d - (codimension s d : ℚ) ≤ (target s : ℚ))

/-- Every feasible source dimension has a source-derived supporting line meeting
the outer and normal incidence inequalities. -/
def CellBounds (m q c cell : ℕ) : Prop :=
  ∀ d : ℤ, Eligible m c cell d →
    ∃ left right : ℕ, LineValid m c cell left right ∧
      IncidenceBounds (scalars m q c)
        (lineBetween (vertex m c cell left) (vertex m c cell right)) d

theorem checkCell_sound (m q c cell : ℕ) (xs : List Chunk)
    (h : checkCell m q c cell xs = true) : CellBounds m q c cell := by
  intro d heligible
  have hd := heligible.in_range
  rcases Bool.and_eq_true_iff.mp h with ⟨hcover, hvalid⟩
  obtain ⟨z, hz, hzlo, hzhi⟩ := checkCover_covers xs
    (dimensionLower m c cell) (dimensionUpper m c cell) hcover d hd.1 hd.2
  have hzvalid : ChunkValid m q c cell z :=
    of_decide_eq_true ((List.all_eq_true.mp hvalid) z hz)
  rcases hzvalid with ⟨hl, ho, hn⟩
  refine ⟨z.payload.left, z.payload.right, hl, ?_⟩
  have hden := hl.2.2.1
  have ho' := ho.nonnegative d hzlo hzhi
  have hn' := hn.nonnegative d hzlo hzhi
  exact ⟨outer_of_quadratic _ _ d hden ho',
    normal_of_quadratic _ _ d _ _ _ hden hn'⟩

/-- Configuration-level arithmetic statement; the four knot intervals are explicit. -/
def ConfigurationBounds (m q c : ℕ) : Prop := ∀ cell : Fin 4, CellBounds m q c cell

theorem configuration_of_cells (m q c : ℕ) (data : Array (List Chunk))
    (h : ∀ cell : Fin 4, checkCell m q c cell (data[cell.val]?.getD []) = true) :
    ConfigurationBounds m q c := by
  intro cell
  exact checkCell_sound m q c cell (data[cell.val]?.getD []) (h cell)

end Quartic.HullCertificate
