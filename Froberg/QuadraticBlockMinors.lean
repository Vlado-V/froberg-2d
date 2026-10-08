import Froberg.PairedMonomials

/-! Three consistent monomial specializations certify the quadratic block
construction: one edge, two adjacent edges, and all three disjoint pairings. -/
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Froberg.QuadraticBlocks
open Finset PairedMonomials ProductMinors

abbrev CanonicalLabel := Fin 6 × Bool

def edgeSupport : Fin 6 → Finset (Fin 4) :=
  ![{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}]

def canonicalTerms (l : CanonicalLabel) : Finset ((Fin 4 × Bool) →₀ ℕ) :=
  (edgeSupport l.1).powerset.image (pairedExponent (edgeSupport l.1))

def choiceSubset (l : CanonicalLabel) : Finset (Fin 4) :=
  if l.2 then ![{1}, {2}, {0, 3}, {2}, {1}, {2, 3}] l.1
    else ![∅, ∅, {0}, ∅, ∅, {3}] l.1

def canonicalChoice (l : CanonicalLabel) : (Fin 4 × Bool) →₀ ℕ :=
  pairedExponent (edgeSupport l.1) (choiceSubset l)

def choiceCoordinates (l : CanonicalLabel) (z : Fin 4 × Bool) : ℕ :=
  if z.2 then (if z.1 ∈ edgeSupport l.1 ∩ choiceSubset l then 1 else 0)
    else (if z.1 ∈ edgeSupport l.1 \ choiceSubset l then 1 else 0)

theorem canonicalChoice_apply (l : CanonicalLabel) (z : Fin 4 × Bool) :
    canonicalChoice l z = choiceCoordinates l z := by
  rcases z with ⟨i, b⟩
  cases b <;> simp [canonicalChoice, choiceCoordinates]

theorem choiceSubset_subset : ∀ l : CanonicalLabel, choiceSubset l ⊆ edgeSupport l.1 := by
  decide +kernel

theorem canonicalChoice_mem (l : CanonicalLabel) : canonicalChoice l ∈ canonicalTerms l := by
  exact mem_image.mpr ⟨choiceSubset l, mem_powerset.mpr (choiceSubset_subset l), rfl⟩

def sameLeft : Fin 3 → CanonicalLabel := ![(0, false), (0, false), (0, true)]
def sameRight : Fin 3 → CanonicalLabel := ![(0, false), (0, true), (0, true)]

def adjacentLeft (i : Bool × Bool) : CanonicalLabel := (0, i.1)
def adjacentRight (i : Bool × Bool) : CanonicalLabel := (1, i.2)

def disjointLeft (i : Fin 3 × Bool × Bool) : CanonicalLabel := (![0, 1, 2] i.1, i.2.1)
def disjointRight (i : Fin 3 × Bool × Bool) : CanonicalLabel := (![5, 4, 3] i.1, i.2.2)

theorem same_coordinates_injective : Function.Injective
    (fun i : Fin 3 => choiceCoordinates (sameLeft i) + choiceCoordinates (sameRight i)) := by
  decide +kernel

theorem adjacent_coordinates_injective : Function.Injective
    (fun i : Bool × Bool => choiceCoordinates (adjacentLeft i) + choiceCoordinates (adjacentRight i)) := by
  decide +kernel

theorem disjoint_coordinates_injective : Function.Injective
    (fun i : Fin 3 × Bool × Bool => choiceCoordinates (disjointLeft i) + choiceCoordinates (disjointRight i)) := by
  decide +kernel

theorem choices_injective_of_coordinates {ι : Type*} (left right : ι → CanonicalLabel)
    (h : Function.Injective (fun i => choiceCoordinates (left i) + choiceCoordinates (right i))) :
    Function.Injective (fun i => canonicalChoice (left i) + canonicalChoice (right i)) := by
  intro i j hij
  apply h
  funext z
  have hh := congrArg (fun p : (Fin 4 × Bool) →₀ ℕ => p z) hij
  simpa only [Finsupp.add_apply, canonicalChoice_apply, Pi.add_apply] using hh

theorem same_choices_injective : Function.Injective
    (fun i : Fin 3 => canonicalChoice (sameLeft i) + canonicalChoice (sameRight i)) :=
  choices_injective_of_coordinates sameLeft sameRight same_coordinates_injective

theorem adjacent_choices_injective : Function.Injective
    (fun i : Bool × Bool => canonicalChoice (adjacentLeft i) + canonicalChoice (adjacentRight i)) :=
  choices_injective_of_coordinates adjacentLeft adjacentRight adjacent_coordinates_injective

theorem disjoint_choices_injective : Function.Injective
    (fun i : Fin 3 × Bool × Bool => canonicalChoice (disjointLeft i) + canonicalChoice (disjointRight i)) :=
  choices_injective_of_coordinates disjointLeft disjointRight disjoint_coordinates_injective

/-- A choice for every possible block-degree fiber on at most four vertices.
The only fiber involving three different matchings is the disjoint one. -/
def fiberSubset (I : Finset (Fin 4)) (l : CanonicalLabel) : Finset (Fin 4) :=
  if I.card = 0 then choiceSubset l
  else if l.2 then (if I.card = 1 then edgeSupport l.1 \ I else edgeSupport l.1)
  else ∅

def fiberCoordinates (I : Finset (Fin 4)) (l : CanonicalLabel)
    (z : Fin 4 × Bool) : ℕ :=
  if z.2 then (if z.1 ∈ edgeSupport l.1 ∩ fiberSubset I l then 1 else 0)
  else (if z.1 ∈ edgeSupport l.1 \ fiberSubset I l then 1 else 0)

theorem fiberSubset_subset (I : Finset (Fin 4)) (l : CanonicalLabel) :
    fiberSubset I l ⊆ edgeSupport l.1 := by
  unfold fiberSubset
  split_ifs <;> first | exact choiceSubset_subset l | exact sdiff_subset | rfl | exact empty_subset _

/-- The finite certificate includes all three four-vertex matchings with their
shared form coefficients, as well as every adjacent and diagonal fiber. -/
theorem fiber_coordinates_injective : ∀ a b c d : CanonicalLabel,
    edgeSupport a.1 ∩ edgeSupport b.1 = edgeSupport c.1 ∩ edgeSupport d.1 →
    edgeSupport a.1 ∪ edgeSupport b.1 = edgeSupport c.1 ∪ edgeSupport d.1 →
    fiberCoordinates (edgeSupport a.1 ∩ edgeSupport b.1) a +
      fiberCoordinates (edgeSupport a.1 ∩ edgeSupport b.1) b =
    fiberCoordinates (edgeSupport a.1 ∩ edgeSupport b.1) c +
      fiberCoordinates (edgeSupport a.1 ∩ edgeSupport b.1) d →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  decide +kernel

theorem edgeSupport_bijective : Function.Bijective
    (fun i : Fin 6 => (⟨edgeSupport i, by fin_cases i <;> decide⟩ :
      ProductFibers.SizedSubset (Fin 4) 2)) := by
  constructor <;> decide +kernel

variable {K : Type*} [CommRing K] [Nontrivial K]

theorem same_minor_nonzero :
    (productMinor (K := K) canonicalTerms sameLeft sameRight
      (fun i => canonicalChoice (sameLeft i) + canonicalChoice (sameRight i))).det ≠ 0 :=
  productMinor_ne_zero canonicalTerms sameLeft sameRight canonicalChoice
    (fun _ => canonicalChoice_mem _) (fun _ => canonicalChoice_mem _) same_choices_injective

theorem adjacent_minor_nonzero :
    (productMinor (K := K) canonicalTerms adjacentLeft adjacentRight
      (fun i => canonicalChoice (adjacentLeft i) + canonicalChoice (adjacentRight i))).det ≠ 0 :=
  productMinor_ne_zero canonicalTerms adjacentLeft adjacentRight canonicalChoice
    (fun _ => canonicalChoice_mem _) (fun _ => canonicalChoice_mem _) adjacent_choices_injective

theorem disjoint_minor_nonzero :
    (productMinor (K := K) canonicalTerms disjointLeft disjointRight
      (fun i => canonicalChoice (disjointLeft i) + canonicalChoice (disjointRight i))).det ≠ 0 :=
  productMinor_ne_zero canonicalTerms disjointLeft disjointRight canonicalChoice
    (fun _ => canonicalChoice_mem _) (fun _ => canonicalChoice_mem _) disjoint_choices_injective

end Froberg.QuadraticBlocks
