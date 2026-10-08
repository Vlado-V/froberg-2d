import Quartic.SharpCertificate.Arithmetic

/-! A small, fully checked certificate for all integer dimensions on one sharp edge. -/

namespace Quartic.SharpCertificate

open Quartic.HullCertificate Quartic.ProfileCertificate

structure Mode where
  first : Bool
  second : Bool
  strict : Bool
  deriving Repr

abbrev Chunk := Interval Mode

def modeAt (s : Scalars) (d : ℤ) : Mode :=
  let first := decide (0 < s.k - 4*d)
  let second := decide (0 < s.S - s.c*d)
  ⟨first, second, decide (target s < 0) && !first && !second⟩

/-- Clamp an integer to a closed interval. -/
def clip (lo hi x : ℤ) : ℤ := max lo (min hi x)

/-- At most three intervals, split at the two coefficient-codimension breakpoints.
The soundness proof checks coverage explicitly and does not trust this algorithm. -/
def automaticIntervals (s : Scalars) (lo hi : ℤ) : List Chunk :=
  let firstBreak := (s.k + 3) / 4
  let secondBreak := (s.S + s.c - 1) / s.c
  let cut₁ := clip lo (hi + 1) (min firstBreak secondBreak)
  let cut₂ := clip lo (hi + 1) (max firstBreak secondBreak)
  [⟨lo, cut₁ - 1, modeAt s lo⟩,
   ⟨cut₁, cut₂ - 1, modeAt s cut₁⟩,
   ⟨cut₂, hi, modeAt s cut₂⟩].filter fun z => decide (z.lo ≤ z.hi)

def edgeLower (m c i : ℕ) (edge : Fin 6) : ℤ :=
  max 1 ((i : ℤ) + (edgeLeft edge : ℤ) * (freeW m c : ℤ))

def edgeUpper (m c i : ℕ) (edge : Fin 6) : ℤ :=
  min ((totalA m c : ℤ) - 1) ((i : ℤ) + (edgeRight edge : ℤ) * (freeW m c : ℤ))

/-- The integral source dimension and intermediate layer lie in the manuscript ranges. -/
def Eligible (m c i : ℕ) (edge : Fin 6) (d : ℤ) : Prop :=
  1 ≤ d ∧ d < (totalA m c : ℤ) ∧
    (i : ℤ) + (edgeLeft edge : ℤ) * (freeW m c : ℤ) ≤ d ∧
    d ≤ (i : ℤ) + (edgeRight edge : ℤ) * (freeW m c : ℤ)

theorem Eligible.in_range {m c i : ℕ} {edge : Fin 6} {d : ℤ}
    (h : Eligible m c i edge d) : edgeLower m c i edge ≤ d ∧ d ≤ edgeUpper m c i edge := by
  unfold Eligible at h
  unfold edgeLower edgeUpper
  omega

def ChunkValid (s : Scalars) (D : ℤ) (f : Cubic) (z : Chunk) : Prop :=
  (outerPolynomial s D f).Valid z.lo z.hi ∧
    (normalPolynomial s D f z.payload.first z.payload.second z.payload.strict).Valid z.lo z.hi

instance (s : Scalars) (D : ℤ) (f : Cubic) (z : Chunk) : Decidable (ChunkValid s D f z) := by
  unfold ChunkValid
  infer_instance

/-- An executable small certificate; all polynomial and interval arithmetic is integral. -/
def checkEdge (m q c i : ℕ) (edge : Fin 6) : Bool :=
  let s := scalars m q c
  let lo := edgeLower m c i edge
  let hi := edgeUpper m c i edge
  let xs := automaticIntervals s lo hi
  checkCover lo hi xs &&
    xs.all fun z => decide (ChunkValid s (edgeScale edge) (edgePolynomial (parameters m c i) edge) z)

/-- Both source incidence tests at every eligible integral dimension on one rational edge. -/
def EdgeBounds (m q c i : ℕ) (edge : Fin 6) : Prop :=
  ∀ d : ℤ, Eligible m c i edge d →
    ImageBounds (scalars m q c) (sharpEdge (parameters m c i) edge d) d

theorem checkEdge_sound (m q c i : ℕ) (edge : Fin 6)
    (h : checkEdge m q c i edge = true) : EdgeBounds m q c i edge := by
  intro d hd
  have hr := hd.in_range
  rcases Bool.and_eq_true_iff.mp h with ⟨hcover, hvalid⟩
  obtain ⟨z, hz, hlo, hhi⟩ := checkCover_covers _
    (edgeLower m c i edge) (edgeUpper m c i edge) hcover d hr.1 hr.2
  have hzvalid : ChunkValid (scalars m q c) (edgeScale edge)
      (edgePolynomial (parameters m c i) edge) z :=
    of_decide_eq_true ((List.all_eq_true.mp hvalid) z hz)
  have ho := hzvalid.1.nonnegative d hlo hhi
  have hn := hzvalid.2.nonnegative d hlo hhi
  rw [sharpEdge_eq_quotient]
  exact imageBounds_of_polynomials _ _ _ _ _ _ _ (edgeScale_pos edge) ho hn

/-- Every core dimension and all six prefix edges are certified. -/
def ConfigurationBounds (m q c : ℕ) : Prop :=
  ∀ i : Fin (coreA c + 1), ∀ edge : Fin 6, EdgeBounds m q c i edge

theorem configuration_of_checks (m q c : ℕ)
    (h : ∀ i : Fin (coreA c + 1), ∀ edge : Fin 6, checkEdge m q c i edge = true) :
    ConfigurationBounds m q c := by
  intro i edge
  exact checkEdge_sound m q c i edge (h i edge)

end Quartic.SharpCertificate
