import Froberg.PairedMonomials

/-! Five finite monomial certificates for two unrestricted multilinear quartics
per four-element support.  The assignments are data; every property below is
proved by kernel reduction against the actual coordinate formula. -/
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Froberg.QuarticBlocks
open Finset PairedMonomials ProductFibers
abbrev CanonicalLabel := Fin 70 × Bool

def canonicalSupport : Fin 70 → Finset (Fin 8) :=
  ![{0, 1, 2, 3},
    {0, 1, 2, 4},
    {0, 1, 2, 5},
    {0, 1, 2, 6},
    {0, 1, 2, 7},
    {0, 1, 3, 4},
    {0, 1, 3, 5},
    {0, 1, 3, 6},
    {0, 1, 3, 7},
    {0, 1, 4, 5},
    {0, 1, 4, 6},
    {0, 1, 4, 7},
    {0, 1, 5, 6},
    {0, 1, 5, 7},
    {0, 1, 6, 7},
    {0, 2, 3, 4},
    {0, 2, 3, 5},
    {0, 2, 3, 6},
    {0, 2, 3, 7},
    {0, 2, 4, 5},
    {0, 2, 4, 6},
    {0, 2, 4, 7},
    {0, 2, 5, 6},
    {0, 2, 5, 7},
    {0, 2, 6, 7},
    {0, 3, 4, 5},
    {0, 3, 4, 6},
    {0, 3, 4, 7},
    {0, 3, 5, 6},
    {0, 3, 5, 7},
    {0, 3, 6, 7},
    {0, 4, 5, 6},
    {0, 4, 5, 7},
    {0, 4, 6, 7},
    {0, 5, 6, 7},
    {1, 2, 3, 4},
    {1, 2, 3, 5},
    {1, 2, 3, 6},
    {1, 2, 3, 7},
    {1, 2, 4, 5},
    {1, 2, 4, 6},
    {1, 2, 4, 7},
    {1, 2, 5, 6},
    {1, 2, 5, 7},
    {1, 2, 6, 7},
    {1, 3, 4, 5},
    {1, 3, 4, 6},
    {1, 3, 4, 7},
    {1, 3, 5, 6},
    {1, 3, 5, 7},
    {1, 3, 6, 7},
    {1, 4, 5, 6},
    {1, 4, 5, 7},
    {1, 4, 6, 7},
    {1, 5, 6, 7},
    {2, 3, 4, 5},
    {2, 3, 4, 6},
    {2, 3, 4, 7},
    {2, 3, 5, 6},
    {2, 3, 5, 7},
    {2, 3, 6, 7},
    {2, 4, 5, 6},
    {2, 4, 5, 7},
    {2, 4, 6, 7},
    {2, 5, 6, 7},
    {3, 4, 5, 6},
    {3, 4, 5, 7},
    {3, 4, 6, 7},
    {3, 5, 6, 7},
    {4, 5, 6, 7}]

def selectedSubsets : Fin 5 → Fin 70 → (Finset (Fin 8) × Finset (Fin 8)) :=
  ![![(∅, {0, 1, 3}), ({0, 2}, {0, 2, 4}), ({0}, {1, 5}), ({0, 2}, {1, 6}), ({0}, {7}), (∅, {1}), ({0, 1, 5}, {1, 3, 5}), ({6}, {0, 6}), ({3}, {0, 1, 3, 7}), (∅, {4, 5}), ({0, 1}, {4}), ({0, 1, 4}, {1, 4, 7}), ({0, 1}, {0, 6}), ({0, 5}, {0, 7}), ({7}, {0, 1, 6, 7}), ({0}, {0, 2, 4}), ({0}, {0, 5}), ({2}, {3}), ({0, 2, 3}, {7}), ({2}, {4}), ({6}, {0, 2, 6}), ({4}, {0, 2, 4}), ({2, 5}, {2, 6}), ({0, 2, 7}, {0, 2, 5, 7}), ({7}, {0, 6, 7}), ({0, 5}, {3, 5}), ({3, 6}, {0, 3, 4, 6}), ({0}, {3, 4}), ({0, 5}, {0, 3, 6}), ({0, 5}, {0, 3, 5, 7}), ({0, 3, 7}, {0, 6, 7}), ({0, 4, 5}, {6}), ({7}, {0, 4, 5, 7}), ({4}, {4, 7}), ({5, 6}, {0, 5, 6, 7}), ({1}, {1, 2, 3}), (∅, {2, 3}), ({2, 3}, {3, 6}), ({1, 3}, {1, 2, 7}), ({4}, {1, 4}), ({1, 2, 4}, {1, 2, 4, 6}), ({7}, {4, 7}), ({6}, {1, 2, 6}), ({1, 2}, {2, 7}), ({2}, {1, 2, 7}), ({1}, {1, 3}), ({3, 6}, {1, 4, 6}), ({3, 4}, {1, 3, 4, 7}), ({1, 3}, {1, 3, 5}), ({3}, {1, 3, 7}), ({1}, {1, 7}), ({4, 6}, {1, 4, 5, 6}), (∅, {7}), ({1, 6}, {1, 4, 6}), (∅, {1, 7}), ({3, 4}, {2, 5}), ({2, 3}, {2, 4}), ({3}, {2, 4}), ({2, 6}, {3, 5, 6}), ({5}, {2, 3, 5, 7}), ({6}, {2, 3, 6}), ({2}, {4, 5, 6}), ({2}, {5, 7}), ({2}, {4, 7}), ({2, 5}, {6, 7}), ({3, 5}, {3, 5, 6}), ({3, 4, 7}, {5, 7}), ({7}, {4, 7}), ({6, 7}, {5, 6, 7}), ({4, 6}, {4, 5, 7})],
    ![({0, 1, 2}, {1, 2, 3}), ({2, 4}, {0, 2, 4}), ({0, 1}, {1, 5}), ({0, 6}, {1, 6}), (∅, ∅), ({3}, {1, 4}), ({0, 3}, {5}), ({0}, {0, 3}), (∅, ∅), ({0, 4}, {5}), ({1}, {4, 6}), (∅, ∅), ({0, 5, 6}, {1, 5, 6}), (∅, ∅), (∅, ∅), ({0, 2, 3}, {0, 3, 4}), ({0, 3, 5}, {2, 3, 5}), ({0}, {3}), (∅, ∅), ({0}, {0, 2}), ({2, 4}, {0, 6}), (∅, ∅), ({0, 2}, {6}), (∅, ∅), (∅, ∅), ({0, 3, 4}, {0, 4, 5}), ({3}, {4}), (∅, ∅), ({0, 5}, {3, 6}), (∅, ∅), (∅, ∅), ({4, 5}, {4, 6}), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅)],
    ![({0, 3}, {2, 3}), ({1, 4}, {0, 1, 4}), ({0, 1, 2}, {0, 1, 5}), (∅, ∅), (∅, ∅), ({0, 1}, {0, 3}), (∅, {3}), (∅, ∅), (∅, ∅), ({1}, {0, 1, 4, 5}), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅)],
    ![({1, 3}, {0, 2, 3}), ({1, 4}, {0, 1, 4}), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅)],
    ![({1, 2}, {1, 2, 3}), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅), (∅, ∅)]]

def choiceSubset (r : Fin 5) (l : CanonicalLabel) : Finset (Fin 8) :=
  if l.2 then (selectedSubsets r l.1).2 else (selectedSubsets r l.1).1

def choiceCoordinates (r : Fin 5) (l : CanonicalLabel) (z : Fin 8 × Bool) : ℕ :=
  if z.2 then (if z.1 ∈ canonicalSupport l.1 ∩ choiceSubset r l then 1 else 0)
  else (if z.1 ∈ canonicalSupport l.1 \ choiceSubset r l then 1 else 0)

def initialSet (k : ℕ) : Finset (Fin 8) := univ.filter (fun i => i.val < k)

def sourceColumns : Fin 5 → List (CanonicalLabel × CanonicalLabel) :=
  ![[((0, false), (69, false)), ((0, false), (69, true)), ((0, true), (69, false)), ((0, true), (69, true)), ((1, false), (68, false)), ((1, false), (68, true)), ((1, true), (68, false)), ((1, true), (68, true)), ((2, false), (67, false)), ((2, false), (67, true)), ((2, true), (67, false)), ((2, true), (67, true)), ((3, false), (66, false)), ((3, false), (66, true)), ((3, true), (66, false)), ((3, true), (66, true)), ((4, false), (65, false)), ((4, false), (65, true)), ((4, true), (65, false)), ((4, true), (65, true)), ((5, false), (64, false)), ((5, false), (64, true)), ((5, true), (64, false)), ((5, true), (64, true)), ((6, false), (63, false)), ((6, false), (63, true)), ((6, true), (63, false)), ((6, true), (63, true)), ((7, false), (62, false)), ((7, false), (62, true)), ((7, true), (62, false)), ((7, true), (62, true)), ((8, false), (61, false)), ((8, false), (61, true)), ((8, true), (61, false)), ((8, true), (61, true)), ((9, false), (60, false)), ((9, false), (60, true)), ((9, true), (60, false)), ((9, true), (60, true)), ((10, false), (59, false)), ((10, false), (59, true)), ((10, true), (59, false)), ((10, true), (59, true)), ((11, false), (58, false)), ((11, false), (58, true)), ((11, true), (58, false)), ((11, true), (58, true)), ((12, false), (57, false)), ((12, false), (57, true)), ((12, true), (57, false)), ((12, true), (57, true)), ((13, false), (56, false)), ((13, false), (56, true)), ((13, true), (56, false)), ((13, true), (56, true)), ((14, false), (55, false)), ((14, false), (55, true)), ((14, true), (55, false)), ((14, true), (55, true)), ((15, false), (54, false)), ((15, false), (54, true)), ((15, true), (54, false)), ((15, true), (54, true)), ((16, false), (53, false)), ((16, false), (53, true)), ((16, true), (53, false)), ((16, true), (53, true)), ((17, false), (52, false)), ((17, false), (52, true)), ((17, true), (52, false)), ((17, true), (52, true)), ((18, false), (51, false)), ((18, false), (51, true)), ((18, true), (51, false)), ((18, true), (51, true)), ((19, false), (50, false)), ((19, false), (50, true)), ((19, true), (50, false)), ((19, true), (50, true)), ((20, false), (49, false)), ((20, false), (49, true)), ((20, true), (49, false)), ((20, true), (49, true)), ((21, false), (48, false)), ((21, false), (48, true)), ((21, true), (48, false)), ((21, true), (48, true)), ((22, false), (47, false)), ((22, false), (47, true)), ((22, true), (47, false)), ((22, true), (47, true)), ((23, false), (46, false)), ((23, false), (46, true)), ((23, true), (46, false)), ((23, true), (46, true)), ((24, false), (45, false)), ((24, false), (45, true)), ((24, true), (45, false)), ((24, true), (45, true)), ((25, false), (44, false)), ((25, false), (44, true)), ((25, true), (44, false)), ((25, true), (44, true)), ((26, false), (43, false)), ((26, false), (43, true)), ((26, true), (43, false)), ((26, true), (43, true)), ((27, false), (42, false)), ((27, false), (42, true)), ((27, true), (42, false)), ((27, true), (42, true)), ((28, false), (41, false)), ((28, false), (41, true)), ((28, true), (41, false)), ((28, true), (41, true)), ((29, false), (40, false)), ((29, false), (40, true)), ((29, true), (40, false)), ((29, true), (40, true)), ((30, false), (39, false)), ((30, false), (39, true)), ((30, true), (39, false)), ((30, true), (39, true)), ((31, false), (38, false)), ((31, false), (38, true)), ((31, true), (38, false)), ((31, true), (38, true)), ((32, false), (37, false)), ((32, false), (37, true)), ((32, true), (37, false)), ((32, true), (37, true)), ((33, false), (36, false)), ((33, false), (36, true)), ((33, true), (36, false)), ((33, true), (36, true)), ((34, false), (35, false)), ((34, false), (35, true)), ((34, true), (35, false)), ((34, true), (35, true))],
    [((0, false), (31, false)), ((0, false), (31, true)), ((0, true), (31, false)), ((0, true), (31, true)), ((1, false), (28, false)), ((1, false), (28, true)), ((1, true), (28, false)), ((1, true), (28, true)), ((2, false), (26, false)), ((2, false), (26, true)), ((2, true), (26, false)), ((2, true), (26, true)), ((3, false), (25, false)), ((3, false), (25, true)), ((3, true), (25, false)), ((3, true), (25, true)), ((5, false), (22, false)), ((5, false), (22, true)), ((5, true), (22, false)), ((5, true), (22, true)), ((6, false), (20, false)), ((6, false), (20, true)), ((6, true), (20, false)), ((6, true), (20, true)), ((7, false), (19, false)), ((7, false), (19, true)), ((7, true), (19, false)), ((7, true), (19, true)), ((9, false), (17, false)), ((9, false), (17, true)), ((9, true), (17, false)), ((9, true), (17, true)), ((10, false), (16, false)), ((10, false), (16, true)), ((10, true), (16, false)), ((10, true), (16, true)), ((12, false), (15, false)), ((12, false), (15, true)), ((12, true), (15, false)), ((12, true), (15, true))],
    [((0, false), (9, false)), ((0, false), (9, true)), ((0, true), (9, false)), ((0, true), (9, true)), ((1, false), (6, false)), ((1, false), (6, true)), ((1, true), (6, false)), ((1, true), (6, true)), ((2, false), (5, false)), ((2, false), (5, true)), ((2, true), (5, false)), ((2, true), (5, true))],
    [((0, false), (1, false)), ((0, false), (1, true)), ((0, true), (1, false)), ((0, true), (1, true))],
    [((0, false), (0, false)), ((0, false), (0, true)), ((0, true), (0, true))]]

theorem choiceSubset_subset : ∀ (r : Fin 5) (l : CanonicalLabel),
    choiceSubset r l ⊆ canonicalSupport l.1 := by decide +kernel

theorem canonicalSupport_card : ∀ i : Fin 70, (canonicalSupport i).card = 4 := by
  decide +kernel

theorem canonicalSupport_bijective : Function.Bijective
    (fun i : Fin 70 => (⟨canonicalSupport i, canonicalSupport_card i⟩ : SizedSubset (Fin 8) 4)) := by
  constructor <;> decide +kernel

/-- The enumerated columns cover every unordered source in the canonical fiber. -/
theorem sourceColumns_cover_mem : ∀ (r : Fin 5) (a b : CanonicalLabel),
    canonicalSupport a.1 ∩ canonicalSupport b.1 = initialSet r.val →
    canonicalSupport a.1 ∪ canonicalSupport b.1 = initialSet (8-r.val) →
    (a,b) ∈ sourceColumns r ∨ (b,a) ∈ sourceColumns r := by
  decide +kernel

theorem sourceColumns_cover (r : Fin 5) (a b : CanonicalLabel)
    (hI : canonicalSupport a.1 ∩ canonicalSupport b.1 = initialSet r.val)
    (hU : canonicalSupport a.1 ∪ canonicalSupport b.1 = initialSet (8-r.val)) :
    ∃ i : Fin (sourceColumns r).length,
      (sourceColumns r)[i] = (a,b) ∨ (sourceColumns r)[i] = (b,a) := by
  rcases sourceColumns_cover_mem r a b hI hU with h | h
  · obtain ⟨i,hi⟩ := List.mem_iff_get.mp h
    exact ⟨i, Or.inl hi⟩
  · obtain ⟨i,hi⟩ := List.mem_iff_get.mp h
    exact ⟨i, Or.inr hi⟩

/-- Distinct source columns specialize to distinct genuine product exponents. -/
theorem sourceColumns_products_injective : ∀ r : Fin 5,
    Function.Injective (fun i : Fin (sourceColumns r).length =>
      choiceCoordinates r (sourceColumns r)[i].1 +
        choiceCoordinates r (sourceColumns r)[i].2) := by
  decide +kernel

end Froberg.QuarticBlocks
