module

public import Froberg.QuadraticBlockChoices

@[expose] public section

/-! Each product fiber lives on at most four blocks.  Restricting to those
blocks transfers the finite consistent-monomial certificate to arbitrary size. -/
noncomputable section
namespace Froberg.QuadraticBlocks
open Finset PairedMonomials ProductFibers
variable {X : Type*} [Fintype X] [DecidableEq X]

abbrev BoundedLabel (U : Finset X) := {l : Label X // support l ⊆ U}

def restrictLabel (U : Finset X) (l : BoundedLabel U) : Label U :=
  (⟨(support l.val).subtype (· ∈ U), by
    rw [card_subtype, filter_true_of_mem (fun x hx => l.property hx), card_support]⟩, l.val.2)

@[simp] theorem restrictLabel_support (U : Finset X) (l : BoundedLabel U) :
    (support (restrictLabel U l)).map (Function.Embedding.subtype (· ∈ U)) = support l.val :=
  Finset.subtype_map_of_mem (fun x hx => l.property hx)

theorem restrictLabel_injective (U : Finset X) : Function.Injective (restrictLabel U) := by
  intro l m h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change support l.val = support m.val
    have h' := congrArg (fun z : Label U =>
      (support z).map (Function.Embedding.subtype (· ∈ U))) h
    simpa only [restrictLabel_support] using h'
  · exact congrArg (fun z : Label U => z.2) h

def liftSubset (U : Finset X) (A : Finset U) : Finset X :=
  A.map (Function.Embedding.subtype (· ∈ U))

@[simp] theorem mem_liftSubset (U : Finset X) (A : Finset U) (x : U) :
    x.val ∈ liftSubset U A ↔ x ∈ A := by simp [liftSubset]

def liftedChoice (U : Finset X) (e : U ↪ Fin 4) (I : Finset U)
    (l : BoundedLabel U) : (X × Bool) →₀ ℕ :=
  pairedExponent (support l.val) (liftSubset U (localSubset e I (restrictLabel U l)))

theorem liftedChoice_mem (U : Finset X) (e : U ↪ Fin 4) (I : Finset U)
    (l : BoundedLabel U) : liftedChoice U e I l ∈ terms l.val := by
  apply mem_image.mpr
  refine ⟨liftSubset U (localSubset e I (restrictLabel U l)), mem_powerset.mpr ?_, rfl⟩
  rw [← restrictLabel_support U l]
  exact Finset.map_subset_map.mpr (localSubset_subset e I (restrictLabel U l))

@[simp] theorem liftedChoice_apply (U : Finset X) (e : U ↪ Fin 4) (I : Finset U)
    (l : BoundedLabel U) (x : U) (b : Bool) :
    liftedChoice U e I l (x.val,b) = localChoice e I (restrictLabel U l) (x,b) := by
  have hs : x.val ∈ support l.val ↔ x ∈ support (restrictLabel U l) := by
    change x.val ∈ support l.val ↔ x ∈ (support l.val).subtype (· ∈ U)
    simp
  cases b <;> simp [liftedChoice, localChoice, hs]

/-- The consistent choices on a small vertex set extend to all global form
labels; only labels used by the fiber need be prescribed. -/
theorem exists_global_fiber_choices (I U : Finset X) (hIU : I ⊆ U) (hU : U.card ≤ 4) :
    ∃ choice : Label X → (X × Bool) →₀ ℕ,
      (∀ l, support l ⊆ U → choice l ∈ terms l) ∧
      ∀ a b c d : Label X,
        support a ∩ support b = I → support a ∪ support b = U →
        support c ∩ support d = I → support c ∪ support d = U →
        choice a + choice b = choice c + choice d → s(a,b) = s(c,d) := by
  classical
  obtain ⟨e⟩ : Nonempty (U ↪ Fin 4) := Function.Embedding.nonempty_of_card_le
    (by simpa using hU)
  let I' : Finset U := I.subtype (· ∈ U)
  let g : BoundedLabel U → (X × Bool) →₀ ℕ := liftedChoice U e I'
  let choice : Label X → (X × Bool) →₀ ℕ :=
    Function.extend Subtype.val g (fun _ => 0)
  have hchoice (l : BoundedLabel U) : choice l.val = g l :=
    Subtype.val_injective.extend_apply g (fun _ => 0) l
  refine ⟨choice, ?_, ?_⟩
  · intro l hl
    rw [hchoice ⟨l,hl⟩]
    exact liftedChoice_mem U e I' ⟨l,hl⟩
  · intro a b c d habI habU hcdI hcdU hp
    have ha : support a ⊆ U := habU ▸ Finset.subset_union_left
    have hb : support b ⊆ U := habU ▸ Finset.subset_union_right
    have hc : support c ⊆ U := hcdU ▸ Finset.subset_union_left
    have hd : support d ⊆ U := hcdU ▸ Finset.subset_union_right
    let a' : BoundedLabel U := ⟨a,ha⟩
    let b' : BoundedLabel U := ⟨b,hb⟩
    let c' : BoundedLabel U := ⟨c,hc⟩
    let d' : BoundedLabel U := ⟨d,hd⟩
    have hiab : support (restrictLabel U a') ∩ support (restrictLabel U b') = I' := by
      apply Finset.map_injective (Function.Embedding.subtype (· ∈ U))
      rw [Finset.map_inter, restrictLabel_support, restrictLabel_support]
      exact habI.trans (Finset.subtype_map_of_mem (fun x hx => hIU hx)).symm
    have hicd : support (restrictLabel U c') ∩ support (restrictLabel U d') = I' := by
      apply Finset.map_injective (Function.Embedding.subtype (· ∈ U))
      rw [Finset.map_inter, restrictLabel_support, restrictLabel_support]
      exact hcdI.trans (Finset.subtype_map_of_mem (fun x hx => hIU hx)).symm
    have hu : support (restrictLabel U a') ∪ support (restrictLabel U b') =
        support (restrictLabel U c') ∪ support (restrictLabel U d') := by
      apply Finset.map_injective (Function.Embedding.subtype (· ∈ U))
      rw [Finset.map_union, Finset.map_union, restrictLabel_support, restrictLabel_support,
        restrictLabel_support, restrictLabel_support]
      exact habU.trans hcdU.symm
    have hlp : localChoice e I' (restrictLabel U a') + localChoice e I' (restrictLabel U b') =
        localChoice e I' (restrictLabel U c') + localChoice e I' (restrictLabel U d') := by
      ext ⟨x,t⟩
      have h := congrArg (fun p : (X × Bool) →₀ ℕ => p (x.val,t)) hp
      rw [hchoice a',hchoice b',hchoice c',hchoice d'] at h
      simpa only [g, Finsupp.add_apply, liftedChoice_apply] using h
    rw [← hiab] at hlp
    have heq := localChoice_pair_injective e (restrictLabel U a') (restrictLabel U b')
      (restrictLabel U c') (restrictLabel U d') (hiab.trans hicd.symm) hu hlp
    have hbounded : s(a',b') = s(c',d') :=
      Sym2.map.injective (restrictLabel_injective U) heq
    exact congrArg (Sym2.map Subtype.val) hbounded

end Froberg.QuadraticBlocks
