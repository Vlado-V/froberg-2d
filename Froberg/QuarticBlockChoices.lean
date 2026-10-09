module

public import Froberg.QuarticBlockRelabeling

@[expose] public section

/-! The five concrete quartic certificates give consistent monomial choices
on every normalized product fiber. -/
noncomputable section
namespace Froberg.QuarticBlocks
open Finset PairedMonomials ProductFibers
abbrev Label (X : Type*) [Fintype X] [DecidableEq X] := SizedSubset X 4 × Bool
variable {X : Type*} [Fintype X] [DecidableEq X]

def support (l : Label X) : Finset X := l.1.val
@[simp] theorem card_support (l : Label X) : (support l).card = 4 := l.1.property

def terms (l : Label X) : Finset ((X × Bool) →₀ ℕ) :=
  (support l).powerset.image (pairedExponent (support l))

def supportEquiv : Fin 70 ≃ SizedSubset (Fin 8) 4 :=
  Equiv.ofBijective _ canonicalSupport_bijective

def canonicalLabel (e : X ↪ Fin 8) (l : Label X) : CanonicalLabel :=
  (supportEquiv.symm ⟨(support l).map e, by rw [card_map, card_support]⟩, l.2)

@[simp] theorem canonicalLabel_support (e : X ↪ Fin 8) (l : Label X) :
    canonicalSupport (canonicalLabel e l).1 = (support l).map e :=
  congrArg Subtype.val (supportEquiv.apply_symm_apply _)

@[simp] theorem canonicalLabel_slot (e : X ↪ Fin 8) (l : Label X) :
    (canonicalLabel e l).2 = l.2 := rfl

theorem canonicalLabel_injective (e : X ↪ Fin 8) : Function.Injective (canonicalLabel e) := by
  intro l m h
  apply Prod.ext
  · apply Subtype.ext
    apply Finset.map_injective e
    change (support l).map e = (support m).map e
    simpa only [canonicalLabel_support] using congrArg (fun z => canonicalSupport z.1) h
  · simpa only [canonicalLabel_slot] using congrArg (fun z : CanonicalLabel => z.2) h

theorem canonical_pair_injective (r : Fin 5) (a b c d : CanonicalLabel)
    (habI : canonicalSupport a.1 ∩ canonicalSupport b.1 = initialSet r.val)
    (habU : canonicalSupport a.1 ∪ canonicalSupport b.1 = initialSet (8-r.val))
    (hcdI : canonicalSupport c.1 ∩ canonicalSupport d.1 = initialSet r.val)
    (hcdU : canonicalSupport c.1 ∪ canonicalSupport d.1 = initialSet (8-r.val))
    (hp : choiceCoordinates r a + choiceCoordinates r b =
      choiceCoordinates r c + choiceCoordinates r d) : s(a,b) = s(c,d) := by
  obtain ⟨i,hi⟩ := sourceColumns_cover r a b habI habU
  obtain ⟨j,hj⟩ := sourceColumns_cover r c d hcdI hcdU
  have he : i = j := by
    apply sourceColumns_products_injective r
    rcases hi with hi | hi <;> rcases hj with hj | hj <;>
      simp only [hi,hj] <;> simpa only [add_comm] using hp
  subst j
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · have hh := hi.symm.trans hj
    exact congrArg (fun p : CanonicalLabel × CanonicalLabel => s(p.1,p.2)) hh
  · have hh := hi.symm.trans hj
    exact (congrArg (fun p : CanonicalLabel × CanonicalLabel => s(p.1,p.2)) hh).trans Sym2.eq_swap
  · have hh := hi.symm.trans hj
    exact Sym2.eq_swap.trans (congrArg (fun p : CanonicalLabel × CanonicalLabel => s(p.1,p.2)) hh)
  · have hh := hi.symm.trans hj
    exact Sym2.eq_swap.trans ((congrArg (fun p : CanonicalLabel × CanonicalLabel => s(p.1,p.2)) hh).trans Sym2.eq_swap)

def localSubset (e : X ↪ Fin 8) (r : Fin 5) (l : Label X) : Finset X :=
  univ.filter (fun x => e x ∈ choiceSubset r (canonicalLabel e l))

theorem localSubset_subset (e : X ↪ Fin 8) (r : Fin 5) (l : Label X) :
    localSubset e r l ⊆ support l := by
  intro x hx
  have he := choiceSubset_subset r (canonicalLabel e l) (mem_filter.mp hx).2
  rw [canonicalLabel_support] at he
  simpa using he

def localChoice (e : X ↪ Fin 8) (r : Fin 5) (l : Label X) : (X × Bool) →₀ ℕ :=
  pairedExponent (support l) (localSubset e r l)

theorem localChoice_mem (e : X ↪ Fin 8) (r : Fin 5) (l : Label X) :
    localChoice e r l ∈ terms l :=
  mem_image.mpr ⟨localSubset e r l, mem_powerset.mpr (localSubset_subset e r l), rfl⟩

theorem localChoice_apply (e : X ↪ Fin 8) (r : Fin 5) (l : Label X) (x : X) (b : Bool) :
    localChoice e r l (x,b) = choiceCoordinates r (canonicalLabel e l) (e x,b) := by
  cases b <;> simp [localChoice, choiceCoordinates, canonicalLabel_support, localSubset]

theorem choiceCoordinates_zero_of_notMem_range (e : X ↪ Fin 8) (r : Fin 5)
    (l : Label X) (x : Fin 8) (hx : x ∉ Set.range e) (b : Bool) :
    choiceCoordinates r (canonicalLabel e l) (x,b) = 0 := by
  have hs : x ∉ canonicalSupport (canonicalLabel e l).1 := by
    rw [canonicalLabel_support]
    rintro h
    obtain ⟨y,hy,rfl⟩ := mem_map.mp h
    exact hx ⟨y,rfl⟩
  cases b <;> simp only [choiceCoordinates, Bool.false_eq_true, reduceIte,
    Finset.mem_inter, Finset.mem_sdiff, hs, false_and]

/-- Distinct unordered products in the normalized fiber stay distinct after
pulling the consistent canonical monomials back along the vertex embedding. -/
theorem localChoice_pair_injective (e : X ↪ Fin 8) (I : Finset X) (r : Fin 5)
    (heI : I.map e = initialSet r.val)
    (heU : (univ : Finset X).map e = initialSet (8-r.val))
    (a b c d : Label X)
    (habI : support a ∩ support b = I) (habU : support a ∪ support b = univ)
    (hcdI : support c ∩ support d = I) (hcdU : support c ∪ support d = univ)
    (hp : localChoice e r a + localChoice e r b = localChoice e r c + localChoice e r d) :
    s(a,b) = s(c,d) := by
  have hcoordinates : choiceCoordinates r (canonicalLabel e a) + choiceCoordinates r (canonicalLabel e b) =
      choiceCoordinates r (canonicalLabel e c) + choiceCoordinates r (canonicalLabel e d) := by
    funext ⟨x,t⟩
    by_cases hx : x ∈ Set.range e
    · obtain ⟨y,rfl⟩ := hx
      have h := congrArg (fun p : (X × Bool) →₀ ℕ => p (y,t)) hp
      simpa only [Finsupp.add_apply, localChoice_apply, Pi.add_apply] using h
    · simp only [Pi.add_apply, choiceCoordinates_zero_of_notMem_range e _ _ x hx t]
  have h := canonical_pair_injective r (canonicalLabel e a) (canonicalLabel e b)
    (canonicalLabel e c) (canonicalLabel e d)
    (by simp only [canonicalLabel_support, ← Finset.map_inter,habI,heI])
    (by simp only [canonicalLabel_support, ← Finset.map_union,habU,heU])
    (by simp only [canonicalLabel_support, ← Finset.map_inter,hcdI,heI])
    (by simp only [canonicalLabel_support, ← Finset.map_union,hcdU,heU]) hcoordinates
  exact Sym2.map.injective (canonicalLabel_injective e) h

end Froberg.QuarticBlocks
