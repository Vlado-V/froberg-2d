import Froberg.PreparedAllEvenCounts
import Froberg.PreparedAppend

/-! The appended quadratic labels that carry the restored pure family in
even degree. These are actual slots of the prepared coefficient space. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg MvPolynomial

theorem allEvenCount_append {d : ℕ} (hd : 3≤d) (h n e u : ℕ) :
    allEvenCount d h n (e+u)=appendedCounts (allEvenCount d h n e) u 2 := by
  funext j
  by_cases hj : j=2
  · subst j
    simp [allEvenCount_active h n _ (two_mem_activeEvenIndices hd),
      targetLayerCount,ite_true,appendedCounts]
  · by_cases hactive : j∈activeEvenIndices d
    · simp [allEvenCount_active h n _ hactive,targetLayerCount,if_neg hj,
        appendedCounts,add_zero]
    · simp only [allEvenCount_inactive h n _ hactive,appendedCounts,if_neg hj,add_zero]

def quadraticTailSlot {d : ℕ} (hd : 3≤d) (q h n e u : ℕ) :
    Fin u → Label q (allEvenIndices d) (allEvenCount d h n (e+u)) :=
  fun k => Sum.inr ⟨⟨2,mem_allEvenIndices.mpr ⟨le_rfl,by omega,by decide⟩⟩,
    Fin.cast (by simp [allEvenCount_active h n _ (two_mem_activeEvenIndices hd),
      targetLayerCount,ite_true]) (Fin.natAdd e k)⟩

@[simp] theorem quadraticTailSlot_degree {d : ℕ} (hd : 3≤d) (q h n e u : ℕ)
    (k : Fin u) : degree (quadraticTailSlot hd q h n e u k)=2 := rfl

theorem quadraticTailSlot_injective {d : ℕ} (hd : 3≤d) (q h n e u : ℕ) :
    Function.Injective (quadraticTailSlot hd q h n e u) := by
  intro k l hkl
  have hh := congrArg (fun i : Label q (allEvenIndices d) (allEvenCount d h n (e+u)) =>
    Sum.elim (fun _ => 0) (fun a => a.2.val) i) hkl
  change e+k.val=e+l.val at hh
  exact Fin.ext (Nat.add_left_cancel hh)

theorem quadraticTailSlot_generator {K : Type} [Field K] [Infinite K]
    {σ : Type*} [Fintype σ] {d : ℕ} (hd : 3≤d) (q h n e u : ℕ)
    {O : ℕ → Submodule K (MvPolynomial σ K)}
    (p : Space n d q (allEvenIndices d) (allEvenCount d h n (e+u)) O) (k : Fin u) :
    generator p (quadraticTailSlot hd q h n e u k)=
      rename Sum.inr (p.1 (quadraticTailSlot hd q h n e u k)).val+
      (p.2 ⟨2,mem_allEvenIndices.mpr ⟨le_rfl,by omega,by decide⟩⟩
        (Fin.cast (by simp [allEvenCount_active h n _ (two_mem_activeEvenIndices hd),
          targetLayerCount,ite_true]) (Fin.natAdd e k))).val := rfl

end Froberg.PreparedParameters
