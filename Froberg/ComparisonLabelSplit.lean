import Froberg.CriticalComparisonCounts
import Froberg.PreparedPureSlots

/-! The temporary quadratic column is an actual extra label. Removing it
before replacement restores the exact critical cardinality. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg

def quadraticAppendLabelEquiv {d : ℕ} (hd : 3 ≤ d) (q h m e extra : ℕ) :
    Label q (allEvenIndices d) (allEvenCount d h m e) ⊕ Fin extra ≃
      Label q (allEvenIndices d) (allEvenCount d h m (e+extra)) := by
  rw [allEvenCount_append hd h m e extra]
  exact appendLabelEquiv ⟨2,mem_allEvenIndices.mpr ⟨le_rfl,by omega,by decide⟩⟩

def comparisonExtraLabelEquiv {d : ℕ} (hd : 3 ≤ d) (q h m e f extra : ℕ) :
    (Label q (allEvenIndices d) (allEvenCount d h m e) ⊕ Fin f) ⊕ Fin extra ≃
      Label q (allEvenIndices d) (allEvenCount d h m (e+extra)) ⊕ Fin f :=
  (Equiv.sumAssoc _ _ _).trans
    ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
      ((Equiv.sumAssoc _ _ _).symm.trans
        (Equiv.sumCongr (quadraticAppendLabelEquiv hd q h m e extra) (Equiv.refl _))))

end Froberg.PreparedParameters
