module

public import Froberg.QuadraticBlockMinors

@[expose] public section

/-! Transport of the finite quadratic block certificates to arbitrary sets of
at most four vertices, retaining one consistent monomial for each form label. -/
noncomputable section
namespace Froberg.QuadraticBlocks
open Finset PairedMonomials ProductFibers

abbrev Label (X : Type*) [Fintype X] [DecidableEq X] := SizedSubset X 2 × Bool

variable {X : Type*} [Fintype X] [DecidableEq X]

def support (l : Label X) : Finset X := l.1.val

@[simp] theorem card_support (l : Label X) : (support l).card = 2 := l.1.property

def terms (l : Label X) : Finset ((X × Bool) →₀ ℕ) :=
  (support l).powerset.image (pairedExponent (support l))

def edgeEquiv : Fin 6 ≃ SizedSubset (Fin 4) 2 :=
  Equiv.ofBijective _ edgeSupport_bijective

def canonicalLabel (e : X ↪ Fin 4) (l : Label X) : CanonicalLabel :=
  (edgeEquiv.symm ⟨(support l).map e, by rw [card_map, card_support]⟩, l.2)

@[simp] theorem canonicalLabel_support (e : X ↪ Fin 4) (l : Label X) :
    edgeSupport (canonicalLabel e l).1 = (support l).map e :=
  congrArg Subtype.val (edgeEquiv.apply_symm_apply _)

@[simp] theorem canonicalLabel_slot (e : X ↪ Fin 4) (l : Label X) :
    (canonicalLabel e l).2 = l.2 := rfl

theorem canonicalLabel_injective (e : X ↪ Fin 4) : Function.Injective (canonicalLabel e) := by
  intro l m h
  apply Prod.ext
  · apply Subtype.ext
    apply Finset.map_injective e
    change (support l).map e = (support m).map e
    simpa only [canonicalLabel_support] using congrArg (fun z => edgeSupport z.1) h
  · simpa only [canonicalLabel_slot] using congrArg (fun z : CanonicalLabel => z.2) h

def pullbackSubset (e : X ↪ Fin 4) (S : Finset (Fin 4)) : Finset X :=
  Finset.univ.filter (fun x => e x ∈ S)

@[simp] theorem mem_pullbackSubset (e : X ↪ Fin 4) (S : Finset (Fin 4)) (x : X) :
    x ∈ pullbackSubset e S ↔ e x ∈ S := by simp [pullbackSubset]

def localSubset (e : X ↪ Fin 4) (I : Finset X) (l : Label X) : Finset X :=
  pullbackSubset e (fiberSubset (I.map e) (canonicalLabel e l))

theorem localSubset_subset (e : X ↪ Fin 4) (I : Finset X) (l : Label X) :
    localSubset e I l ⊆ support l := by
  intro x hx
  have he := fiberSubset_subset (I.map e) (canonicalLabel e l)
    ((mem_pullbackSubset _ _ _).mp hx)
  rw [canonicalLabel_support] at he
  simpa using he

def localChoice (e : X ↪ Fin 4) (I : Finset X) (l : Label X) : (X × Bool) →₀ ℕ :=
  pairedExponent (support l) (localSubset e I l)

theorem localChoice_mem (e : X ↪ Fin 4) (I : Finset X) (l : Label X) :
    localChoice e I l ∈ terms l :=
  mem_image.mpr ⟨localSubset e I l, mem_powerset.mpr (localSubset_subset e I l), rfl⟩

theorem localChoice_apply (e : X ↪ Fin 4) (I : Finset X) (l : Label X) (x : X) (b : Bool) :
    localChoice e I l (x,b) = fiberCoordinates (I.map e) (canonicalLabel e l) (e x,b) := by
  cases b <;>
    simp [localChoice, fiberCoordinates, canonicalLabel_support, localSubset]

theorem fiberCoordinates_zero_of_notMem_range (e : X ↪ Fin 4) (I : Finset X)
    (l : Label X) (x : Fin 4) (hx : x ∉ Set.range e) (b : Bool) :
    fiberCoordinates (I.map e) (canonicalLabel e l) (x,b) = 0 := by
  have hs : x ∉ edgeSupport (canonicalLabel e l).1 := by
    rw [canonicalLabel_support]
    rintro h
    obtain ⟨y, hy, rfl⟩ := mem_map.mp h
    exact hx ⟨y, rfl⟩
  cases b <;> simp only [fiberCoordinates, Bool.false_eq_true, reduceIte,
    Finset.mem_inter, Finset.mem_sdiff, hs, false_and]

/-- Every fiber has a consistent monomial specialization with all unordered
products distinct, whenever the vertex set embeds into four vertices. -/
theorem localChoice_pair_injective (e : X ↪ Fin 4) (a b c d : Label X)
    (hi : support a ∩ support b = support c ∩ support d)
    (hu : support a ∪ support b = support c ∪ support d)
    (hp : localChoice e (support a ∩ support b) a +
        localChoice e (support a ∩ support b) b =
      localChoice e (support a ∩ support b) c +
        localChoice e (support a ∩ support b) d) :
    s(a,b) = s(c,d) := by
  have hci : edgeSupport (canonicalLabel e a).1 ∩ edgeSupport (canonicalLabel e b).1 =
      edgeSupport (canonicalLabel e c).1 ∩ edgeSupport (canonicalLabel e d).1 := by
    simp only [canonicalLabel_support, ← Finset.map_inter, hi]
  have hcu : edgeSupport (canonicalLabel e a).1 ∪ edgeSupport (canonicalLabel e b).1 =
      edgeSupport (canonicalLabel e c).1 ∪ edgeSupport (canonicalLabel e d).1 := by
    simp only [canonicalLabel_support, ← Finset.map_union, hu]
  have hI : (support a ∩ support b).map e =
      edgeSupport (canonicalLabel e a).1 ∩ edgeSupport (canonicalLabel e b).1 := by
    simp only [canonicalLabel_support, Finset.map_inter]
  have hcoordinates :
      fiberCoordinates ((support a ∩ support b).map e) (canonicalLabel e a) +
        fiberCoordinates ((support a ∩ support b).map e) (canonicalLabel e b) =
      fiberCoordinates ((support a ∩ support b).map e) (canonicalLabel e c) +
        fiberCoordinates ((support a ∩ support b).map e) (canonicalLabel e d) := by
    funext ⟨x,t⟩
    by_cases hx : x ∈ Set.range e
    · obtain ⟨y, rfl⟩ := hx
      have h := congrArg (fun p : (X × Bool) →₀ ℕ => p (y,t)) hp
      simpa only [Finsupp.add_apply, localChoice_apply, Pi.add_apply] using h
    · simp only [Pi.add_apply, fiberCoordinates_zero_of_notMem_range e _ _ x hx t]
  rw [hI] at hcoordinates
  have h := fiber_coordinates_injective (canonicalLabel e a) (canonicalLabel e b)
    (canonicalLabel e c) (canonicalLabel e d) hci hcu hcoordinates
  apply Sym2.eq_iff.mpr
  exact h.imp
    (fun h => ⟨canonicalLabel_injective e h.1, canonicalLabel_injective e h.2⟩)
    (fun h => ⟨canonicalLabel_injective e h.1, canonicalLabel_injective e h.2⟩)

end Froberg.QuadraticBlocks
