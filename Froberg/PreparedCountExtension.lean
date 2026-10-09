module

public import Froberg.PreparedPureSlots

@[expose] public section

/-! Enlarge a layer count by extending the coefficient tuple by zero.
The unused tail slots can carry restored pure forms. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg MvPolynomial
variable {q : ℕ} {J : Finset ℕ} {c c' : ℕ → ℕ}

def countLabelMap (hc : ∀ j∈J,c j≤c' j) : Label q J c → Label q J c' :=
  Sum.elim Sum.inl (fun a => Sum.inr ⟨a.1,Fin.castLE (hc _ a.1.property) a.2⟩)

variable {K : Type} [Field K] [Infinite K] {σ : Type*} [Fintype σ]
variable {n d : ℕ} {O : ℕ → Submodule K (MvPolynomial σ K)}

def extendCounts (hc : ∀ j∈J,c j≤c' j) (p : Space n d q J c O) : Space n d q J c' O :=
  (Sum.elim (fun i => p.1 (Sum.inl i)) (fun a =>
    if hi : a.2.val<c a.1.val then p.1 (Sum.inr ⟨a.1,⟨a.2.val,hi⟩⟩) else 0),
    fun j i => if hi : i.val<c j.val then p.2 j ⟨i.val,hi⟩ else 0)

theorem extendCounts_generator_old (hc : ∀ j∈J,c j≤c' j) (p : Space n d q J c O)
    (i : Label q J c) : generator (extendCounts hc p) (countLabelMap hc i)=generator p i := by
  cases i with
  | inl i => rfl
  | inr a =>
    rcases a with ⟨j,i⟩
    simp only [generator,scalar,high,extendCounts,countLabelMap,Sum.elim_inr,Fin.coe_castLE,dif_pos i.isLt]

theorem extendCounts_generator_new (hc : ∀ j∈J,c j≤c' j) (p : Space n d q J c O)
    (j : J) (i : Fin (c' j.val)) (hi : c j.val ≤ i.val) :
    generator (extendCounts hc p) (Sum.inr ⟨j,i⟩)=0 := by
  simp only [generator,scalar,high,extendCounts,Sum.elim_inr,dif_neg (not_lt.mpr hi),
    Submodule.coe_zero,map_zero,zero_add]

theorem allEvenCount_le_append {d : ℕ} (hd : 3≤d) (h n e u : ℕ) (j : ℕ)
    (_hj : j∈allEvenIndices d) : allEvenCount d h n e j≤allEvenCount d h n (e+u) j := by
  rw [allEvenCount_append hd]
  exact Nat.le_add_right _ _

def extendQuadratic {d : ℕ} (hd : 3≤d) (h n e u : ℕ)
    (p : Space n d q (allEvenIndices d) (allEvenCount d h n e) O) :
    Space n d q (allEvenIndices d) (allEvenCount d h n (e+u)) O :=
  extendCounts (allEvenCount_le_append hd h n e u) p

theorem extendQuadratic_tail_zero {d : ℕ} (hd : 3≤d) (h n e u : ℕ)
    (p : Space n d q (allEvenIndices d) (allEvenCount d h n e) O) (i : Fin u) :
    generator (extendQuadratic hd h n e u p) (quadraticTailSlot hd q h n e u i)=0 := by
  apply extendCounts_generator_new
  change allEvenCount d h n e 2≤e+i.val
  simp only [allEvenCount_active h n e (two_mem_activeEvenIndices hd),targetLayerCount,ite_true]
  omega

theorem quadraticTailSlot_ne_old {d : ℕ} (hd : 3≤d) (h n e u : ℕ)
    (k : Fin u) (i : Label q (allEvenIndices d) (allEvenCount d h n e)) :
    quadraticTailSlot hd q h n e u k≠countLabelMap (allEvenCount_le_append hd h n e u) i := by
  intro hi
  rcases i with i | ⟨j,i⟩
  · cases hi
  · have hj : 2=j.val := by
      exact congrArg (fun x : Label q (allEvenIndices d) (allEvenCount d h n (e+u)) => degree x) hi
    have hv := congrArg (fun x : Label q (allEvenIndices d) (allEvenCount d h n (e+u)) =>
      Sum.elim (fun _ => 0) (fun a => a.2.val) x) hi
    change e+k.val=i.val at hv
    have hjc : allEvenCount d h n e j.val=e := by
      rw [←hj]
      simp only [allEvenCount_active h n e (two_mem_activeEvenIndices hd),targetLayerCount,ite_true]
    have hb : i.val<e := by simpa only [hjc] using i.isLt
    omega

end Froberg.PreparedParameters
