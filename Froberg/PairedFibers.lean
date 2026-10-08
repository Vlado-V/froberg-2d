import Froberg.PairedMonomials
import Mathlib.Data.Sym.Card

/-! Finite index-degree fibers for the actual paired-variable family. -/
noncomputable section
namespace Froberg.PairedMonomials
open Finset ProductFibers
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- View a finite subset of R as a subset of the ambient variable indices. -/
def liftPart (R : Finset X) (P : Finset R) : Finset X :=
  P.map (Function.Embedding.subtype _)

@[simp] theorem card_liftPart (R : Finset X) (P : Finset R) :
    (liftPart R P).card = P.card := Finset.card_map _

theorem liftPart_subset (R : Finset X) (P : Finset R) : liftPart R P ⊆ R := by
  intro x hx
  exact Finset.property_of_mem_map_subtype P hx

@[simp] theorem mem_liftPart (R : Finset X) (P : Finset R) (x : R) :
    x.1 ∈ liftPart R P ↔ x ∈ P := by
  simp only [liftPart, Finset.mem_map]
  exact ⟨fun ⟨y, hy, he⟩ => by have := Subtype.ext he; subst y; exact hy,
    fun hx => ⟨x,hx,rfl⟩⟩

theorem liftPart_injective (R : Finset X) : Function.Injective (liftPart R) :=
  Finset.map_injective _

@[simp] theorem liftPart_univ (R : Finset X) : liftPart R Finset.univ = R := by
  ext x
  simp [liftPart]

@[simp] theorem liftPart_compl (R : Finset X) (P : Finset R) :
    liftPart R Pᶜ = R \ liftPart R P := by
  ext x
  by_cases hx : x ∈ R
  · simpa only [mem_liftPart R Pᶜ ⟨x,hx⟩, Finset.mem_compl,
      Finset.mem_sdiff, hx, true_and, mem_liftPart R P ⟨x,hx⟩]
  · have h₁ : x ∉ liftPart R P := fun h => hx (liftPart_subset R P h)
    have h₂ : x ∉ liftPart R Pᶜ := fun h => hx (liftPart_subset R Pᶜ h)
    simp [hx,h₁,h₂]

@[simp] theorem liftPart_inter (R : Finset X) (P Q : Finset R) :
    liftPart R (P ∩ Q) = liftPart R P ∩ liftPart R Q := Finset.map_inter _ _

/-- The possible doubled/single index sets of a product of two degree-s forms. -/
abbrev ProductFiber (X : Type*) [Fintype X] [DecidableEq X] (s : ℕ) :=
  {f : Finset X × Finset X // Disjoint f.1 f.2 ∧ f.1.card ≤ s ∧
    f.2.card = 2 * (s - f.1.card)}

namespace ProductFiber
variable {s : ℕ}

def doubled (F : ProductFiber X s) : Finset X := F.1.1
def single (F : ProductFiber X s) : Finset X := F.1.2
def halfSize (F : ProductFiber X s) : ℕ := s - F.doubled.card

theorem disjoint (F : ProductFiber X s) : Disjoint F.doubled F.single := F.2.1

theorem degree (F : ProductFiber X s) : F.doubled.card + F.halfSize = s := by
  have h := F.2.2.1
  dsimp [doubled,halfSize]
  omega

theorem card_single (F : ProductFiber X s) : F.single.card = 2 * F.halfSize := F.2.2.2

theorem card_indices (F : ProductFiber X s) : Fintype.card F.single = 2 * F.halfSize := by
  simpa using F.card_single

abbrev Columns (F : ProductFiber X s) := ProductFibers.Partition F.card_indices

instance columnsDecidableEq (F : ProductFiber X s) : DecidableEq F.Columns := Classical.decEq _

/-- An oriented source half. -/
def half (F : ProductFiber X s) (p : F.Columns) (b : Bool) : Finset F.single :=
  if b then p.out.1ᶜ else p.out.1

theorem card_half (F : ProductFiber X s) (p : F.Columns) (b : Bool) :
    (F.half p b).card = F.halfSize := by
  cases b
  · exact p.out.2
  · change p.out.1ᶜ.card = _
    rw [Finset.card_compl, F.card_indices, p.out.2]
    omega

/-- The actual global form label I ∪ P belonging to a source half. -/
def label (F : ProductFiber X s) (z : F.Columns × Bool) : SizedSubset X s :=
  ⟨F.doubled ∪ liftPart F.single (F.half z.1 z.2), by
    rw [Finset.card_union_of_disjoint
      (F.disjoint.mono_right (liftPart_subset _ _)), card_liftPart, F.card_half, F.degree]⟩

@[simp] theorem label_false (F : ProductFiber X s) (p : F.Columns) :
    (F.label (p,false)).1 = F.doubled ∪ liftPart F.single p.out.1 := rfl

@[simp] theorem label_true (F : ProductFiber X s) (p : F.Columns) :
    (F.label (p,true)).1 = F.doubled ∪ liftPart F.single p.out.1ᶜ := rfl

/-- The unordered pair of global form labels represented by a column. -/
def column (F : ProductFiber X s) (p : F.Columns) : Sym2 (SizedSubset X s) :=
  s(F.label (p,false), F.label (p,true))

theorem label_inter (F : ProductFiber X s) (p : F.Columns) :
    (F.label (p,false)).1 ∩ (F.label (p,true)).1 = F.doubled := by
  rw [label_false, label_true, liftPart_compl]
  ext x
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
  tauto

theorem label_union (F : ProductFiber X s) (p : F.Columns) :
    (F.label (p,false)).1 ∪ (F.label (p,true)).1 = F.doubled ∪ F.single := by
  rw [label_false, label_true, liftPart_compl]
  ext x
  have h := fun hx : x ∈ liftPart F.single p.out.1 => liftPart_subset _ _ hx
  simp only [Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- Giving a source column either orientation does not change its quotient class. -/
theorem half_represents (F : ProductFiber X s) (p : F.Columns) (b : Bool) :
    (⟦(⟨F.half p b, F.card_half p b⟩ : SizedSubset F.single F.halfSize)⟧ : F.Columns) = p := by
  cases b
  · exact Quotient.out_eq p
  · trans (⟦p.out⟧ : F.Columns)
    · apply Quotient.sound
      exact Or.inr (by apply Subtype.ext; rfl)
    · exact Quotient.out_eq p

/-- In a non-diagonal fiber each global form label occurs in exactly one column. -/
theorem label_injective (F : ProductFiber X s) (ht : 0 < F.halfSize) :
    Function.Injective F.label := by
  intro z z' h
  have hs : F.half z.1 z.2 = F.half z'.1 z'.2 := by
    ext x
    have hi : x.1 ∉ F.doubled := fun hi => Finset.disjoint_left.mp F.disjoint hi x.2
    have he := Finset.ext_iff.mp (congrArg Subtype.val h) x.1
    simpa only [label, Finset.mem_union, hi, false_or, mem_liftPart] using he
  have hp : z.1 = z'.1 := by
    have he : (⟨F.half z.1 z.2, F.card_half z.1 z.2⟩ : SizedSubset F.single F.halfSize) =
        ⟨F.half z'.1 z'.2, F.card_half z'.1 z'.2⟩ := Subtype.ext hs
    have hq := congrArg (fun P => (⟦P⟧ : F.Columns)) he
    simpa only [F.half_represents] using hq
  rcases z with ⟨p,b⟩
  rcases z' with ⟨q,c⟩
  dsimp at hp
  subst q
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < p.out.1.card by rw [p.out.2]; exact ht)
  have hn : p.out.1 ≠ p.out.1ᶜ := by
    intro he
    have hxc : x ∈ p.out.1ᶜ := he ▸ hx
    exact Finset.mem_compl.mp hxc hx
  cases b <;> cases c <;> simp_all [half]

end ProductFiber
end Froberg.PairedMonomials
