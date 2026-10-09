module

public import Quartic.HullCertificate.Certificate
public import Quartic.MarkedIncidence

@[expose] public section

/-! Supporting-line certificates for the incidence problem with one marked
coefficient. The witnesses use the same lines and interval minima as the
ordinary certificates, but the scalar block and total dimension increase by one.
-/

namespace Quartic.MarkedHullCertificate

open Quartic.HullCertificate Quartic.ProfileCertificate

def ChunkValid (m q c cell : ℕ) (z : Chunk) : Prop :=
  let l := chunkLine m c cell z
  let s := markedScalars (scalars m q c)
  LineValid m c cell z.payload.left z.payload.right ∧
    MinimumValid l.denominator (outerLinear s l) l.intercept z.lo z.hi z.payload.outerMinimum ∧
    MinimumValid l.denominator
      (normalLinear s l z.payload.first z.payload.second z.payload.strict)
      (normalConstant s l z.payload.first z.payload.second z.payload.strict)
      z.lo z.hi z.payload.normalMinimum

instance (m q c cell : ℕ) (z : Chunk) : Decidable (ChunkValid m q c cell z) := by
  unfold ChunkValid
  infer_instance

/-- The actual finite certificate checker. All arithmetic is integral. -/
def checkCell (m q c cell : ℕ) (xs : List Chunk) : Bool :=
  checkCover (dimensionLower m c cell) (dimensionUpper m c cell) xs &&
    xs.all fun z => decide (ChunkValid m q c cell z)

/-- Every feasible source dimension has a source-derived supporting line meeting
the outer and normal incidence inequalities. -/
def CellBounds (m q c cell : ℕ) : Prop :=
  ∀ d : ℤ, Eligible m c cell d →
    ∃ left right : ℕ, LineValid m c cell left right ∧
      IncidenceBounds (markedScalars (scalars m q c))
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

end Quartic.MarkedHullCertificate
