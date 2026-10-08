import Froberg.PreparedPureSlots
import Froberg.EvenTail

/-! The pure basis occupies actual appended quadratic slots. Optional
additional quadratic columns do not interfere with these distinguished slots. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module
variable {K : Type} [Field K] {d h m q r e extra : ℕ}

theorem even_tail_eq_finrank (hh : 0 < h) (he : d%2=0) :
    tailGeneratorCount d h=finrank K (Forms K h d) := by
  have hodd : ¬Odd d := by
    intro ho
    have hp := Nat.odd_iff.mp ho
    omega
  rw [tailGeneratorCount,if_neg hodd,finrank_forms K h d hh]

def countedRestorationSlot (hd : 3 ≤ d) (hh : 0 < h) (he : d%2=0)
    (idx : Fin r ≃ Label q (allEvenIndices d)
      (allEvenCount d h m (e+tailGeneratorCount d h+extra))) :
    Fin (finrank K (Forms K h d)) → Fin r := fun i => idx.symm
  (Sum.inr ⟨⟨2,mem_allEvenIndices.mpr ⟨le_rfl,by omega,by decide⟩⟩,
    ⟨e+i.val,by
      have hi := i.isLt
      have hu := even_tail_eq_finrank (K := K) hh he
      have hc : allEvenCount d h m (e+tailGeneratorCount d h+extra) 2=
          e+tailGeneratorCount d h+extra := by
        simp only [allEvenCount_active h m _ (two_mem_activeEvenIndices hd),targetLayerCount,ite_true]
      rw [hc]
      omega⟩⟩)

theorem countedRestorationSlot_degree (hd : 3 ≤ d) (hh : 0 < h) (he : d%2=0)
    (idx : Fin r ≃ Label q (allEvenIndices d)
      (allEvenCount d h m (e+tailGeneratorCount d h+extra)))
    (i : Fin (finrank K (Forms K h d))) :
    degree (idx (countedRestorationSlot hd hh he idx i))=2 := by
  unfold countedRestorationSlot
  rw [Equiv.apply_symm_apply]
  rfl

theorem countedRestorationSlot_injective (hd : 3 ≤ d) (hh : 0 < h) (he : d%2=0)
    (idx : Fin r ≃ Label q (allEvenIndices d)
      (allEvenCount d h m (e+tailGeneratorCount d h+extra))) :
    Function.Injective (countedRestorationSlot (K := K) hd hh he idx) := by
  intro i j hij
  have hij' := congrArg (fun k => Sum.elim (fun _ => 0) (fun a => a.2.val) (idx k)) hij
  simp only [countedRestorationSlot,Equiv.apply_symm_apply,Sum.elim_inr] at hij'
  exact Fin.ext (Nat.add_left_cancel hij')

end Froberg.PreparedParameters
