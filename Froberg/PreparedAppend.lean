module

public import Froberg.PreparedParameters
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Sum

@[expose] public section

/-! Appending the private columns to one positive layer is literal reindexing
of the prepared generator family. This is used at the U=0 specialization. -/
noncomputable section
namespace Froberg.PreparedParameters

/-- Add a finite number of columns to one specified layer. -/
def appendedCounts (counts : ℕ → ℕ) (u R j : ℕ) : ℕ :=
  counts j+if j=R then u else 0

variable {q u : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}

def addedSliceEquiv (R : J) :
    Fin u ≃ (Σ j : J,Fin (if j.val=R.val then u else 0)) := by
  classical
  apply Equiv.ofBijective (fun i => ⟨R,Fin.cast (by simp) i⟩)
  constructor
  · intro i k hik
    have hv := congrArg (fun a => a.2.val) hik
    exact Fin.ext hv
  · rintro ⟨j,i⟩
    have hj : j.val=R.val := by
      by_contra h
      have hi := i.isLt
      simp only [if_neg h] at hi
      omega
    have heq : j=R := Subtype.ext hj
    subst j
    refine ⟨Fin.cast (by simp) i,?_⟩
    congr 1

/-- The original labels followed by the additional columns are precisely the
labels of the enlarged layer. -/
def appendLabelEquiv (R : J) :
    Label q J counts ⊕ Fin u ≃ Label q J (appendedCounts counts u R.val) := by
  classical
  let e : ProductRows.LayerLabel J (appendedCounts counts u R.val) ≃
      ProductRows.LayerLabel J counts ⊕ (Σ j : J,Fin (if j.val=R.val then u else 0)) :=
    (Equiv.sigmaCongrRight (fun j : J => (finSumFinEquiv (m := counts j.val)
      (n := if j.val=R.val then u else 0)).symm)).trans
      (Equiv.sigmaSumDistrib (fun j : J => Fin (counts j.val))
        (fun j : J => Fin (if j.val=R.val then u else 0)))
  exact ((Equiv.sumAssoc (Fin q) (ProductRows.LayerLabel J counts) (Fin u)).trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) (addedSliceEquiv R)))).trans
      (Equiv.sumCongr (Equiv.refl _) e.symm)

end Froberg.PreparedParameters
