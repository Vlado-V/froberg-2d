module

public import Froberg.PreparedExtraColumn
public import Froberg.RestoredExtraColumn
public import Froberg.CountedRestorationSlots
public import Froberg.CriticalComparisonCounts

@[expose] public section

/-! Canonical finite indices for the actual restored even family. The pure
slots occupy the quadratic labels e,...,e+u-1; the temporary extra label is
then e+u. Enlarged pure slots are transported through count restriction. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable (K : Type) [Field K]

abbrev actualRestoredPureCount (d h : ℕ) : ℕ := finrank K (Forms K h d)

def actualRestoredCounts (d h n e extra : ℕ) : ℕ → ℕ :=
  allEvenCount d h n (e+actualRestoredPureCount K d h+extra)

abbrev ActualRestoredLabel (d h n e extra : ℕ) :=
  Label (upperCount n d) (allEvenIndices d) (actualRestoredCounts K d h n e extra)

abbrev actualRestoredSize (d h n e extra : ℕ) :=
  Fintype.card (ActualRestoredLabel K d h n e extra)

def actualRestoredIndex (d h n e extra : ℕ) :
    Fin (actualRestoredSize K d h n e extra) ≃ ActualRestoredLabel K d h n e extra :=
  (Fintype.equivFin _).symm

variable {K} {d h n e : ℕ}

theorem actualRestoredCounts_le (hd : 3≤d) :
    ∀ j∈allEvenIndices d,
      actualRestoredCounts K d h n e 0 j≤actualRestoredCounts K d h n e 1 j :=
  allEvenCount_le_append hd h n (e+actualRestoredPureCount K d h) 1

def actualRestoredBaseSlot (hd : 3≤d) :
    Fin (actualRestoredPureCount K d h) → Fin (actualRestoredSize K d h n e 0) :=
  fun i => (actualRestoredIndex K d h n e 0).symm
    (quadraticTailSlot hd (upperCount n d) h n e (actualRestoredPureCount K d h) i)

def actualRestoredInclusion (hd : 3≤d) :
    Fin (actualRestoredSize K d h n e 0) → Fin (actualRestoredSize K d h n e 1) :=
  countIndexMap (actualRestoredCounts_le hd)
    (actualRestoredIndex K d h n e 0) (actualRestoredIndex K d h n e 1)

/-- This definition is the exact transported slot expression used by restriction. -/
def actualRestoredEnlargedSlot (hd : 3≤d) :
    Fin (actualRestoredPureCount K d h) → Fin (actualRestoredSize K d h n e 1) :=
  actualRestoredInclusion hd ∘ actualRestoredBaseSlot hd

def actualRestoredExtraLayer (hd : 3≤d) :
    ProductRows.LayerLabel (allEvenIndices d) (actualRestoredCounts K d h n e 1) :=
  quadraticExtraLayer hd h n (e+actualRestoredPureCount K d h)

def actualRestoredExtraIndex (hd : 3≤d) : Fin (actualRestoredSize K d h n e 1) :=
  (actualRestoredIndex K d h n e 1).symm (Sum.inr (actualRestoredExtraLayer hd))

@[simp] theorem actualRestoredIndex_baseSlot (hd : 3≤d)
    (i : Fin (actualRestoredPureCount K d h)) :
    actualRestoredIndex K d h n e 0 (actualRestoredBaseSlot hd i)=
      quadraticTailSlot hd (upperCount n d) h n e (actualRestoredPureCount K d h) i := by
  exact (actualRestoredIndex K d h n e 0).apply_symm_apply _

@[simp] theorem actualRestoredBaseSlot_degree (hd : 3≤d)
    (i : Fin (actualRestoredPureCount K d h)) :
    degree (actualRestoredIndex K d h n e 0 (actualRestoredBaseSlot hd i))=2 := by
  rw [actualRestoredIndex_baseSlot]
  rfl

theorem actualRestoredBaseSlot_positive (hd : 3≤d)
    (i : Fin (actualRestoredPureCount K d h)) :
    0<degree (actualRestoredIndex K d h n e 0 (actualRestoredBaseSlot hd i)) := by
  rw [actualRestoredBaseSlot_degree]
  decide

theorem actualRestoredBaseSlot_injective (hd : 3≤d) :
    Function.Injective (actualRestoredBaseSlot (K := K) (h := h) (n := n) (e := e) hd) :=
  (actualRestoredIndex K d h n e 0).symm.injective.comp
    (quadraticTailSlot_injective hd (upperCount n d) h n e (actualRestoredPureCount K d h))

theorem actualRestoredInclusion_injective (hd : 3≤d) :
    Function.Injective (actualRestoredInclusion (K := K) (h := h) (n := n) (e := e) hd) :=
  countIndexMap_injective (actualRestoredCounts_le hd) _ _

theorem actualRestoredEnlargedSlot_injective (hd : 3≤d) :
    Function.Injective (actualRestoredEnlargedSlot (K := K) (h := h) (n := n) (e := e) hd) :=
  (actualRestoredInclusion_injective hd).comp (actualRestoredBaseSlot_injective hd)

@[simp] theorem actualRestoredIndex_inclusion (hd : 3≤d)
    (i : Fin (actualRestoredSize K d h n e 0)) :
    actualRestoredIndex K d h n e 1 (actualRestoredInclusion hd i)=
      countLabelMap (actualRestoredCounts_le hd) (actualRestoredIndex K d h n e 0 i) := by
  exact (actualRestoredIndex K d h n e 1).apply_symm_apply _

@[simp] theorem actualRestoredEnlargedSlot_degree (hd : 3≤d)
    (i : Fin (actualRestoredPureCount K d h)) :
    degree (actualRestoredIndex K d h n e 1 (actualRestoredEnlargedSlot hd i))=2 := by
  change degree (actualRestoredIndex K d h n e 1
    (actualRestoredInclusion hd (actualRestoredBaseSlot hd i)))=2
  rw [actualRestoredIndex_inclusion,actualRestoredIndex_baseSlot]
  rfl

theorem actualRestoredEnlargedSlot_positive (hd : 3≤d)
    (i : Fin (actualRestoredPureCount K d h)) :
    0<degree (actualRestoredIndex K d h n e 1 (actualRestoredEnlargedSlot hd i)) := by
  rw [actualRestoredEnlargedSlot_degree]
  decide

@[simp] theorem actualRestoredExtraLayer_degree (hd : 3≤d) :
    (actualRestoredExtraLayer (K := K) (h := h) (n := n) (e := e) hd).1.val=2 := rfl

@[simp] theorem actualRestoredExtraLayer_position (hd : 3≤d) :
    (actualRestoredExtraLayer (K := K) (h := h) (n := n) (e := e) hd).2.val=
      e+actualRestoredPureCount K d h := rfl

@[simp] theorem actualRestoredEnlargedSlot_position (hd : 3≤d)
    (i : Fin (actualRestoredPureCount K d h)) :
    Sum.elim (fun _ => 0) (fun a => a.2.val)
      (actualRestoredIndex K d h n e 1 (actualRestoredEnlargedSlot hd i))=e+i.val := by
  change Sum.elim (fun _ => 0) (fun a => a.2.val)
    (actualRestoredIndex K d h n e 1
      (actualRestoredInclusion hd (actualRestoredBaseSlot hd i)))=e+i.val
  rw [actualRestoredIndex_inclusion,actualRestoredIndex_baseSlot]
  rfl

/-- The temporary column follows every pure slot in the quadratic layer. -/
theorem actualRestoredExtraLayer_after_pure (hd : 3≤d)
    (i : Fin (actualRestoredPureCount K d h)) :
    Sum.elim (fun _ => 0) (fun a => a.2.val)
      (actualRestoredIndex K d h n e 1 (actualRestoredEnlargedSlot hd i))<
        (actualRestoredExtraLayer (K := K) (h := h) (n := n) (e := e) hd).2.val := by
  rw [actualRestoredEnlargedSlot_position,actualRestoredExtraLayer_position]
  exact Nat.add_lt_add_left i.isLt e

theorem actualRestoredExtraLayer_not_old (hd : 3≤d)
    (i : ProductRows.LayerLabel (allEvenIndices d) (actualRestoredCounts K d h n e 0)) :
    countLayerMap (actualRestoredCounts_le hd) i≠actualRestoredExtraLayer hd :=
  quadraticExtraLayer_not_old hd h n (e+actualRestoredPureCount K d h) i

theorem actualRestoredExtraLayer_cover (hd : 3≤d)
    (i : ProductRows.LayerLabel (allEvenIndices d) (actualRestoredCounts K d h n e 1)) :
    i=actualRestoredExtraLayer hd ∨ ∃ j,countLayerMap (actualRestoredCounts_le hd) j=i := by
  exact (quadraticExtraLayer_cover hd h n (e+actualRestoredPureCount K d h) i).symm

theorem actualRestoredExtraIndex_not_old (hd : 3≤d)
    (i : Fin (actualRestoredSize K d h n e 0)) :
    actualRestoredInclusion hd i≠actualRestoredExtraIndex hd := by
  intro heq
  have heq' := congrArg (actualRestoredIndex K d h n e 1) heq
  rw [actualRestoredIndex_inclusion] at heq'
  change countLabelMap (actualRestoredCounts_le hd) (actualRestoredIndex K d h n e 0 i)=
    actualRestoredIndex K d h n e 1
      ((actualRestoredIndex K d h n e 1).symm (Sum.inr (actualRestoredExtraLayer hd))) at heq'
  rw [Equiv.apply_symm_apply] at heq'
  cases hi : actualRestoredIndex K d h n e 0 i with
  | inl j =>
    simp only [hi,countLabelMap,Sum.elim_inl] at heq'
    cases heq'
  | inr j =>
    rw [hi] at heq'
    exact actualRestoredExtraLayer_not_old hd j (Sum.inr.inj heq')

theorem actualRestoredExtraIndex_ne_pure (hd : 3≤d)
    (i : Fin (actualRestoredPureCount K d h)) :
    actualRestoredEnlargedSlot hd i≠actualRestoredExtraIndex (n := n) (e := e) hd :=
  actualRestoredExtraIndex_not_old hd (actualRestoredBaseSlot hd i)

theorem actualRestoredExtraIndex_cover (hd : 3≤d)
    (i : Fin (actualRestoredSize K d h n e 1)) :
    i=actualRestoredExtraIndex hd ∨ ∃ j,actualRestoredInclusion hd j=i := by
  cases hi : actualRestoredIndex K d h n e 1 i with
  | inl j =>
    right
    refine ⟨(actualRestoredIndex K d h n e 0).symm (Sum.inl j),?_⟩
    apply (actualRestoredIndex K d h n e 1).injective
    rw [actualRestoredIndex_inclusion,Equiv.apply_symm_apply,hi]
    rfl
  | inr j =>
    rcases actualRestoredExtraLayer_cover hd j with hj | ⟨k,hk⟩
    · left
      apply (actualRestoredIndex K d h n e 1).injective
      rw [hi,hj]
      exact ((actualRestoredIndex K d h n e 1).apply_symm_apply _).symm
    · right
      refine ⟨(actualRestoredIndex K d h n e 0).symm (Sum.inr k),?_⟩
      apply (actualRestoredIndex K d h n e 1).injective
      rw [actualRestoredIndex_inclusion,Equiv.apply_symm_apply,hi]
      exact congrArg Sum.inr hk

/-- A positive slot count always belongs to a layer strictly below d. -/
theorem actualRestoredCounts_positive_lt (hd : 3≤d) (extra j : ℕ)
    (hj : 0<actualRestoredCounts K d h n e extra j) : j<d := by
  have ha : j∈activeEvenIndices d := by
    by_contra hn
    change 0<allEvenCount d h n (e+actualRestoredPureCount K d h+extra) j at hj
    rw [allEvenCount_inactive _ _ _ hn] at hj
    omega
  exact (activeEvenIndices_bounds hd ha).2.1

/-- The actual base has the critical size; the enlarged family has one extra. -/
theorem actualRestored_card {k lo a f : ℕ} {upper : Bool}
    (hd : 3≤d) (hh : 0<h) (he : d%2=0)
    (hc : ExactCountConditions d k h lo n a f e upper) (extra : ℕ) :
    actualRestoredSize K d h n e extra+f=
      adjacentCriticalCount upper (n+h) d+extra := by
  have hcard := exact_even_comparison_card hd hc extra
  rw [even_tail_eq_finrank (K := K) hh he,Fintype.card_sum,Fintype.card_fin] at hcard
  exact hcard

theorem actualRestored_final_card {k lo a f : ℕ} {upper : Bool}
    (hd : 3≤d) (hh : 0<h) (he : d%2=0)
    (hc : ExactCountConditions d k h lo n a f e upper) :
    upperCount n d+Fintype.card (ProductRows.LayerLabel (allEvenIndices d)
      (actualRestoredCounts K d h n e 0))+f=adjacentCriticalCount upper (h+n) d := by
  have hcard := actualRestored_card (K := K) hd hh he hc 0
  simpa only [actualRestoredSize,ActualRestoredLabel,Label,Fintype.card_sum,
    Fintype.card_fin,Nat.add_zero,Nat.add_comm n h] using hcard

end Froberg.PreparedParameters
