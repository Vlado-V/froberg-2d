module

public import Froberg.Koszul
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-!
# Linear subspace part of the exact hyperplane replacement

This file proves the intersection and dimension assertions in Section 3 of the
revised manuscript. It does not assume or claim the symmetric-product identity
or the remaining homology identification needed for its full Lemma 3.1.
-/

noncomputable section
namespace Froberg
open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Replacing a vector by a nonzero transverse perturbation remains transverse. -/
theorem perturbed_not_mem_sum (W A : Submodule K V) {f M : V} {ε : K}
    (hf : f ∈ W) (hM : M ∉ W ⊔ A) (hε : ε ≠ 0) :
    f + ε • M ∉ W ⊔ A := by
  intro hg
  apply hM
  apply ((W ⊔ A).smul_mem_iff hε).mp
  simpa using (W ⊔ A).sub_mem hg (show f ∈ W ⊔ A from (show W ≤ W ⊔ A from le_sup_left) hf)

/-- A transverse extra line cannot change the intersection with `A`. -/
theorem transverse_line_inf (W₀ W A : Submodule K V) {g : V}
    (h₀ : W₀ ≤ W) (hg : g ∉ W ⊔ A) :
    (W₀ ⊔ Submodule.span K {g}) ⊓ A = W₀ ⊓ A := by
  have h₀B : W₀ ≤ W ⊔ A := h₀.trans le_sup_left
  have hdis : Disjoint (Submodule.span K {g}) (W ⊔ A) :=
    (Submodule.disjoint_span_singleton_of_notMem hg).symm
  have hB : (W₀ ⊔ Submodule.span K {g}) ⊓ (W ⊔ A) = W₀ := by
    rw [sup_inf_assoc_of_le _ h₀B, hdis.eq_bot, sup_bot_eq]
  calc
    (W₀ ⊔ Submodule.span K {g}) ⊓ A =
        ((W₀ ⊔ Submodule.span K {g}) ⊓ (W ⊔ A)) ⊓ A := by
      rw [inf_assoc, inf_eq_right.mpr (show A ≤ W ⊔ A from le_sup_right)]
    _ = W₀ ⊓ A := by rw [hB]

/-- The chosen complement intersects the child coefficient space in the lower child. -/
theorem complement_inf_child (W A Q Qminus W₀ : Submodule K V) {f : V}
    (hWA : W ⊓ A = Q) (hQ : Q = Qminus ⊔ Submodule.span K {f})
    (hW : W = W₀ ⊔ Submodule.span K {f}) (hQ₀ : Qminus ≤ W₀)
    (hf₀ : f ∉ W₀) : W₀ ⊓ A = Qminus := by
  have h₀W : W₀ ≤ W := by rw [hW]; exact le_sup_left
  have hd : Disjoint (Submodule.span K {f}) W₀ :=
    (Submodule.disjoint_span_singleton_of_notMem hf₀).symm
  calc
    W₀ ⊓ A = (W ⊓ A) ⊓ W₀ := by
      rw [inf_right_comm, inf_eq_right.mpr h₀W]
    _ = (Qminus ⊔ Submodule.span K {f}) ⊓ W₀ := by rw [hWA, hQ]
    _ = Qminus := by rw [sup_inf_assoc_of_le _ hQ₀, hd.eq_bot, sup_bot_eq]

/-- The exact subspace intersection asserted by the manuscript's hyperplane replacement. -/
theorem hyperplane_replacement_inf (W A Q Qminus W₀ : Submodule K V) {f M : V} {ε : K}
    (hWA : W ⊓ A = Q) (hQ : Q = Qminus ⊔ Submodule.span K {f})
    (hW : W = W₀ ⊔ Submodule.span K {f}) (hQ₀ : Qminus ≤ W₀)
    (hf₀ : f ∉ W₀) (hM : M ∉ W ⊔ A) (hε : ε ≠ 0) :
    (W₀ ⊔ Submodule.span K {f + ε • M}) ⊓ A = Qminus := by
  have hfW : f ∈ W := by
    rw [hW]
    exact (show Submodule.span K {f} ≤ W₀ ⊔ Submodule.span K {f} from le_sup_right)
      (Submodule.subset_span (Set.mem_singleton f))
  have h₀W : W₀ ≤ W := by rw [hW]; exact le_sup_left
  rw [transverse_line_inf W₀ W A h₀W (perturbed_not_mem_sum W A hfW hM hε)]
  exact complement_inf_child W A Q Qminus W₀ hWA hQ hW hQ₀ hf₀

/-- A transverse replacement preserves the number of independent generators. -/
theorem hyperplane_replacement_finrank [Module.Finite K V]
    (W A W₀ : Submodule K V) {f M : V} {ε : K}
    (hW : W = W₀ ⊔ Submodule.span K {f}) (hf₀ : f ∉ W₀)
    (hM : M ∉ W ⊔ A) (hε : ε ≠ 0) :
    finrank K (W₀ ⊔ Submodule.span K {f + ε • M} : Submodule K V) = finrank K W := by
  have hfW : f ∈ W := by
    rw [hW]
    exact (show Submodule.span K {f} ≤ W₀ ⊔ Submodule.span K {f} from le_sup_right)
      (Submodule.subset_span (Set.mem_singleton f))
  have h₀W : W₀ ≤ W := by rw [hW]; exact le_sup_left
  have hg : f + ε • M ∉ W₀ := by
    intro h
    exact perturbed_not_mem_sum W A hfW hM hε ((show W ≤ W ⊔ A from le_sup_left) (h₀W h))
  rw [Submodule.finrank_sup_span_singleton hg, hW,
    Submodule.finrank_sup_span_singleton hf₀]

end Froberg
